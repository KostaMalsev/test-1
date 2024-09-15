/*
 * Copyright (c) 2015, 2023, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

#include "precompiled.hpp"
#include "gc/shared/gc_globals.hpp"
#include "gc/z/zGeneration.inline.hpp"
#include "gc/z/zList.inline.hpp"
#include "gc/z/zPage.inline.hpp"
#include "gc/z/zPhysicalMemory.inline.hpp"
#include "gc/z/zRememberedSet.inline.hpp"
#include "gc/z/zVirtualMemory.inline.hpp"
#include "utilities/align.hpp"
#include "utilities/debug.hpp"
#include "utilities/growableArray.hpp"
//#include <bitset> // for bitset manipulation
#include "oops/fieldStreams.inline.hpp"

//#include <functional> //for cuckoo hashing



using namespace std;


ZPage::ZPage(ZPageType type, const ZVirtualMemory& vmem, const ZPhysicalMemory& pmem)
  : _type(type),
    _generation_id(ZGenerationId::young),
    _age(ZPageAge::eden),
    _numa_id((uint8_t)-1),
    _seqnum(0),
    _seqnum_other(0),
    _virtual(vmem),
    _top(to_zoffset_end(start())),
    _livemap(object_max_count()),
    _remembered_set(),
    _last_used(0),
    _physical(pmem),
    _node() {
  assert(!_virtual.is_null(), "Should not be null");
  assert(!_physical.is_null(), "Should not be null");
  assert(_virtual.size() == _physical.size(), "Virtual/Physical size mismatch");
  assert((_type == ZPageType::small && size() == ZPageSizeSmall) ||
         (_type == ZPageType::medium && size() == ZPageSizeMedium) ||
         (_type == ZPageType::large && is_aligned(size(), ZGranuleSize)),
         "Page type/size mismatch");
}

ZPage* ZPage::clone_limited() const {
  // Only copy type and memory layouts. Let the rest be lazily reconstructed when needed.
  return new ZPage(_type, _virtual, _physical);
}

ZPage* ZPage::clone_limited_promote_flipped() const {
  ZPage* const page = new ZPage(_type, _virtual, _physical);

  // The page is still filled with the same objects, need to retain the top pointer.
  page->_top = _top;

  return page;
}

ZGeneration* ZPage::generation() {
  return ZGeneration::generation(_generation_id);
}

const ZGeneration* ZPage::generation() const {
  return ZGeneration::generation(_generation_id);
}

void ZPage::reset_seqnum() {
  Atomic::store(&_seqnum, generation()->seqnum());
  Atomic::store(&_seqnum_other, ZGeneration::generation(_generation_id == ZGenerationId::young ? ZGenerationId::old : ZGenerationId::young)->seqnum());
}

void ZPage::remset_clear() {
  _remembered_set.clear_all();
}

void ZPage::verify_remset_after_reset(ZPageAge prev_age, ZPageResetType type) {
  // Young-to-old reset
  if (prev_age != ZPageAge::old) {
    verify_remset_cleared_previous();
    verify_remset_cleared_current();
    return;
  }

  // Old-to-old reset
  switch (type) {
  case ZPageResetType::Splitting:
    // Page is on the way to be destroyed or reused, delay
    // clearing until the page is reset for Allocation.
    break;

  case ZPageResetType::InPlaceRelocation:
    // Relocation failed and page is being compacted in-place.
    // The remset bits are flipped each young mark start, so
    // the verification code below needs to use the right remset.
    if (ZGeneration::old()->active_remset_is_current()) {
      verify_remset_cleared_previous();
    } else {
      verify_remset_cleared_current();
    }
    break;

  case ZPageResetType::FlipAging:
    fatal("Should not have called this for old-to-old flipping");
    break;

  case ZPageResetType::Allocation:
    verify_remset_cleared_previous();
    verify_remset_cleared_current();
    break;
  };
}

void ZPage::reset_remembered_set() {
  if (is_young()) {
    // Remset not needed
    return;
  }

  // Clearing of remsets is done when freeing a page, so this code only
  // needs to ensure the remset is initialized the first time a page
  // becomes old.
  if (!_remembered_set.is_initialized()) {
    _remembered_set.initialize(size());
  }
}

void ZPage::reset(ZPageAge age, ZPageResetType type) {
  const ZPageAge prev_age = _age;
  _age = age;
  _last_used = 0;

  _generation_id = age == ZPageAge::old
      ? ZGenerationId::old
      : ZGenerationId::young;

  reset_seqnum();

  // Flip aged pages are still filled with the same objects, need to retain the top pointer.
  if (type != ZPageResetType::FlipAging) {
    _top = to_zoffset_end(start());
  }

  reset_remembered_set();
  verify_remset_after_reset(prev_age, type);

  if (type != ZPageResetType::InPlaceRelocation || (prev_age != ZPageAge::old && age == ZPageAge::old)) {
    // Promoted in-place relocations reset the live map,
    // because they clone the page.
    _livemap.reset();
  }
}

void ZPage::finalize_reset_for_in_place_relocation() {
  // Now we're done iterating over the livemaps
  _livemap.reset();
}

void ZPage::reset_type_and_size(ZPageType type) {
  _type = type;
  _livemap.resize(object_max_count());
  _remembered_set.resize(size());
}

ZPage* ZPage::retype(ZPageType type) {
  assert(_type != type, "Invalid retype");
  reset_type_and_size(type);
  return this;
}

ZPage* ZPage::split(size_t split_of_size) {
  return split(type_from_size(split_of_size), split_of_size);
}

ZPage* ZPage::split_with_pmem(ZPageType type, const ZPhysicalMemory& pmem) {
  // Resize this page
  const ZVirtualMemory vmem = _virtual.split(pmem.size());

  reset_type_and_size(type_from_size(_virtual.size()));
  reset(_age, ZPageResetType::Splitting);

  assert(vmem.end() == _virtual.start(), "Should be consecutive");

  log_trace(gc, page)("Split page [" PTR_FORMAT ", " PTR_FORMAT ", " PTR_FORMAT "]",
      untype(vmem.start()),
      untype(vmem.end()),
      untype(_virtual.end()));

  // Create new page
  return new ZPage(type, vmem, pmem);
}

ZPage* ZPage::split(ZPageType type, size_t split_of_size) {
  assert(_virtual.size() > split_of_size, "Invalid split");

  const ZPhysicalMemory pmem = _physical.split(split_of_size);

  return split_with_pmem(type, pmem);
}

ZPage* ZPage::split_committed() {
  // Split any committed part of this page into a separate page,
  // leaving this page with only uncommitted physical memory.
  const ZPhysicalMemory pmem = _physical.split_committed();
  if (pmem.is_null()) {
    // Nothing committed
    return nullptr;
  }

  assert(!_physical.is_null(), "Should not be null");

  return split_with_pmem(type_from_size(pmem.size()), pmem);
}

class ZFindBaseOopClosure : public ObjectClosure {
private:
  volatile zpointer* _p;
  oop _result;

public:
  ZFindBaseOopClosure(volatile zpointer* p)
    : _p(p),
      _result(nullptr) {}

  virtual void do_object(oop obj) {
    const uintptr_t p_int = reinterpret_cast<uintptr_t>(_p);
    const uintptr_t base_int = cast_from_oop<uintptr_t>(obj);
    const uintptr_t end_int = base_int + wordSize * obj->size();
    if (p_int >= base_int && p_int < end_int) {
      _result = obj;
    }
  }

  oop result() const { return _result; }
};

bool ZPage::is_remset_cleared_current() const {
  return _remembered_set.is_cleared_current();
}

bool ZPage::is_remset_cleared_previous() const {
  return _remembered_set.is_cleared_previous();
}

void ZPage::verify_remset_cleared_current() const {
  if (ZVerifyRemembered && !is_remset_cleared_current()) {
    fatal_msg(" current remset bits should be cleared");
  }
}

void ZPage::verify_remset_cleared_previous() const {
  if (ZVerifyRemembered && !is_remset_cleared_previous()) {
    fatal_msg(" previous remset bits should be cleared");
  }
}

void ZPage::clear_remset_current() {
 _remembered_set.clear_current();
}

void ZPage::clear_remset_previous() {
 _remembered_set.clear_previous();
}

void ZPage::swap_remset_bitmaps() {
  _remembered_set.swap_remset_bitmaps();
}

void* ZPage::remset_current() {
  return _remembered_set.current();
}

void ZPage::print_on_msg(outputStream* out, const char* msg) const {
  out->print_cr(" %-6s  " PTR_FORMAT " " PTR_FORMAT " " PTR_FORMAT " %s/%-4u %s%s%s",
                type_to_string(), untype(start()), untype(top()), untype(end()),
                is_young() ? "Y" : "O",
                seqnum(),
                is_allocating()  ? " Allocating " : "",
                is_relocatable() ? " Relocatable" : "",
                msg == nullptr ? "" : msg);
}

void ZPage::print_on(outputStream* out) const {
  print_on_msg(out, nullptr);
}

void ZPage::print() const {
  print_on(tty);
}

void ZPage::verify_live(uint32_t live_objects, size_t live_bytes, bool in_place) const {
  if (!in_place) {
    // In-place relocation has changed the page to allocating
    assert_zpage_mark_state();
  }
  guarantee(live_objects == _livemap.live_objects(), "Invalid number of live objects");
  guarantee(live_bytes == _livemap.live_bytes(), "Invalid number of live bytes");
}

void ZPage::fatal_msg(const char* msg) const {
  stringStream ss;
  print_on_msg(&ss, msg);
  fatal("%s", ss.base());
}



 
size_t shash(const char* str) {
  size_t hash = 5381; // Initial hash value (arbitrary seed)
  while (*str) {
    // Shift the hash left 5 bits and add the character code of the current character
    hash = ((hash << 5) + hash) + (*str);
    str++;
  }
  return hash;
}

size_t hash_fnv1a(const char* str) {
    static const std::size_t FNV_OFFSET_BASIS = 14695981039346656037ULL;
    static const std::size_t FNV_PRIME = 1099511628211ULL;

    size_t hash = FNV_OFFSET_BASIS;
    while (*str) {
        hash ^= static_cast<size_t>(*str);
        hash *= FNV_PRIME;
        ++str;
    }
    return hash;
}



u4 sig2size(Symbol* sig) {
  switch (sig->char_at(0)) {
    case JVM_SIGNATURE_CLASS:
    case JVM_SIGNATURE_ARRAY: return sizeof(address);
    case JVM_SIGNATURE_BOOLEAN:
    case JVM_SIGNATURE_BYTE: return 1;
    case JVM_SIGNATURE_SHORT:
    case JVM_SIGNATURE_CHAR: return 2;
    case JVM_SIGNATURE_INT:
    case JVM_SIGNATURE_FLOAT: return 4;
    case JVM_SIGNATURE_LONG:
    case JVM_SIGNATURE_DOUBLE: return 8;
    default: ShouldNotReachHere(); /* to shut up compiler */ return 0;
  }
}

size_t shallow_size(InstanceKlass* ik){
  
    u4 size = 0;
    for (HierarchicalFieldStream<JavaFieldStream> fld(ik); !fld.done(); fld.next()) {
      if (!fld.access_flags().is_static()) {
         size += sig2size(fld.signature());
      }
    }
    size += 16;//the size of the header of the instance

    size_t padd = (size % 8);
    padd = padd == 0 ? 0 : 8 - padd;
    size += padd; //adding padding
    
    return size;
}


const int TABLE_SIZE = 1000;//1000
const int MAX_LOOP = 3;

struct Entry {
    size_t key;
    size_t sum;
    size_t count;
    bool occupied;

    Entry() : key(0), sum(0), count(0), occupied(false) {}
};

class CuckooHashTable {
private:
    Entry table1[TABLE_SIZE];
    Entry table2[TABLE_SIZE];

    size_t hash1(size_t key) {
        return key % TABLE_SIZE;
    }

    size_t hash2(size_t key) {
        return (key / TABLE_SIZE) % TABLE_SIZE;
    }

    void swap(size_t& a, size_t& b){
        size_t temp = a;
        a = b;
        b = temp;
    }

public:
    CuckooHashTable() {}

    bool insert(size_t key, size_t value) {
        size_t curKey = key;
        size_t curValue = value;
        
        for (size_t i = 0; i < MAX_LOOP; ++i) {
            size_t index1 = hash1(curKey);
            if (index1 < 0 || index1 >= TABLE_SIZE) {
                // Invalid index, handle error
                return false;
            }
            if (!table1[index1].occupied) {
                table1[index1].key = curKey;
                table1[index1].sum = curValue;
                table1[index1].count = 1;
                table1[index1].occupied = true;
                return true;
            }
            
            if (table1[index1].key == curKey) {
                table1[index1].sum += curValue;
                table1[index1].count++;
                return true;
            }
            
            swap(curKey, table1[index1].key);
            swap(curValue, table1[index1].sum);
            size_t tempCount = table1[index1].count;
            table1[index1].count = 1;
            curValue += tempCount;

            size_t index2 = hash2(curKey);
            if (index2 < 0 || index2 >= TABLE_SIZE) {
                // Invalid index, handle error
                return false;
            }
            if (!table2[index2].occupied) {
                table2[index2].key = curKey;
                table2[index2].sum = curValue;
                table2[index2].count = tempCount;
                table2[index2].occupied = true;
                return true;
            }
            
            if (table2[index2].key == curKey) {
                table2[index2].sum += curValue;
                table2[index2].count += tempCount;
                return true;
            }
            
            swap(curKey, table2[index2].key);
            swap(curValue, table2[index2].sum);
            swap(tempCount, table2[index2].count);
        }
        
        return false; // Insertion failed after MAX_LOOP iterations
    }

    bool get(size_t key, size_t& sum, size_t& count) {
        size_t index1 = hash1(key);
        if (table1[index1].occupied && table1[index1].key == key) {
            sum = table1[index1].sum;
            count = table1[index1].count;
            return true;
        }

        size_t index2 = hash2(key);
        if (table2[index2].occupied && table2[index2].key == key) {
            sum = table2[index2].sum;
            count = table2[index2].count;
            return true;
        }

        return false;
    }

    void remove(size_t key) {
        size_t index1 = hash1(key);
        if (table1[index1].occupied && table1[index1].key == key) {
            table1[index1].occupied = false;
            return;
        }

        size_t index2 = hash2(key);
        if (table2[index2].occupied && table2[index2].key == key) {
            table2[index2].occupied = false;
            return;
        }
    }
    
    bool update(size_t key, size_t value) {
        size_t index1 = hash1(key);
        if (table1[index1].occupied && table1[index1].key == key) {
            table1[index1].sum += value;
            table1[index1].count++;
            return true;
        }

        size_t index2 = hash2(key);
        if (table2[index2].occupied && table2[index2].key == key) {
            table2[index2].sum += value;
            table2[index2].count++;
            return true;
        }

        // Key not found, insert a new entry
        return insert(key, value);
    }

    int loadFactorPercent() const {
        size_t totalOccupied = 0;
        for (const auto& entry : table1) {
            if (entry.occupied) {
                totalOccupied++;
            }
        }
        for (const auto& entry : table2) {
            if (entry.occupied) {
                totalOccupied++;
            }
        }
        double rawLoadFactor = static_cast<double>(totalOccupied) / (TABLE_SIZE * 2);
        return static_cast<int>(round(rawLoadFactor * 100));
    }
};






void ZPage::page_obj_stats() const {
  
  BitMap::idx_t curr_segment = _livemap.first_live_segment();

  //Storing all different instance type name which incountered in this LiveMap of this page:
  
  //const int N = 10000;//1000000;

  CuckooHashTable hashTable;

  //std::bitset<N> data;
  //data.reset();

  //for testing:
  int distinctCount = 0;
  int hashAccuracyCount = 0;
  int invalidCount = 0;

  /*size_t hashVals[N];
  memset(hashVals, 0, sizeof(hashVals));

  size_t bitPosVals[N];
  memset(bitPosVals, 0, sizeof(hashVals));*/

  int pos = 0;
  //-----------

  //Itirate over the live segments in the page:
  while(curr_segment < 64)
  {

      //Itirate on all bits in the live segments in the page:
      const BitMap::idx_t start_index = _livemap.segment_start(curr_segment);
      const BitMap::idx_t end_index   = _livemap.segment_end(curr_segment);
          
      BitMap::idx_t curr_seg_index = start_index;
      
      //Itirate over the live bits in the segment:
      while(curr_seg_index < end_index )
      {
        BitMap::idx_t liveBitInd = _livemap.first_set_bit(curr_seg_index, end_index);
            
        //Process the bit:
        oopDesc* obj_ref = object_from_bit_index(liveBitInd);


        //--------------TEST for invalid memory access:
          bool test1 = (obj_ref == nullptr);
          bool test2 = obj_ref->is_instanceRef();
          bool test3 = !(obj_ref->klass() == nullptr);

          
          bool test5 = obj_ref->is_array();//pass
          bool test6 = obj_ref->is_objArray();//pass
          bool test7 = obj_ref->is_typeArray();//pass
          bool test8 = oopDesc::is_oop(obj_ref);//pass
          
          bool test9 = obj_ref->is_stackChunk();//pass
          bool test10 = obj_ref->is_instance();//pass

          
          bool test12 = !(obj_ref->klass_or_null() == nullptr);//pass

          bool test14 = obj_ref->is_gc_marked();//pass

          //bool test15 = (obj_ref != nullptr) && (obj_ref->klass()->java_mirror_no_keepalive() == nullptr);//failed 

          bool test16 = (obj_ref != nullptr) && (Klass::is_valid( obj_ref->klass() )); //pass

          bool test17 = test16 && obj_ref->klass()->is_klass();//pass

          bool test18 = test16 && (obj_ref->size() > 0);//pass

          if((obj_ref != nullptr) && !(Klass::is_valid( obj_ref->klass() ))){
            invalidCount++;
            //log_info(gc, heap)("[KOSTA]: invalid #pointers=%d, index=%zu, adress: %016lx segment:%zu",invalidCount, liveBitInd,p2i(obj_ref),curr_segment);
          }

          if((obj_ref != nullptr) && (Klass::is_valid( obj_ref->klass() ))){

            const char* str = obj_ref->klass()->external_name();

            InstanceKlass* ik = InstanceKlass::cast(obj_ref->klass());
            const char* loader_name = ik->class_loader_data()->loader_name_and_id();
    
            const size_t sha = shash(str);
            //const size_t bitPosition = sha % N;

           //if(!data[bitPosition]){
            size_t sum, count;

            if(!hashTable.get(sha, count, sum)){
                distinctCount++;

                //log_info(gc, heap)("[KOSTA]:class size:%zu name len:%zu,loader:%s", obj_ref->size(),strlen(str),loader_name);

                if(strstr(loader_name,"app")!=nullptr){
                  //loader is bootstrap
                  //loader is plattform
                  //loader is app
                  //if( (strstr(str, "KostaClass")!=nullptr) || (strstr(str, "MemoryConsumer")!=nullptr) || (strstr(str, "Professor")!=nullptr) ){
                    //The shallow size of the object is the size of its reference + sizes of its fields.
                    //The retained size will be sum of all retained sized of the objects it references.

                    //log_info(gc, heap)("KOSTA: found class:%s size: %zu", str,obj_ref->size()*HeapWordSize); //scaled by word size in bits (HeapWordSize)
                    log_info(gc, heap)("KOSTA: boots class: %s size: %zu, loader:%s",
                        //str,obj_ref->size(), loader_name); //scaled by word size in bits (HeapWordSize) 
                        str, shallow_size(ik), loader_name); //scaled by word size in bits (HeapWordSize)
                }
                //log_info(gc, heap)("[KOSTA]:class:%s size:%zu hash:%zu object_count:%d segment:%zu livebit:%zu",
                //                  str, obj_ref->size(),bitPosition ,distinctCount, curr_segment,liveBitInd);

                //log_info(gc, heap)("[KOSTA]:class %s size:%zu name len:%zu,loader:%s", str, obj_ref->size(),strlen(str),loader_name);

                hashTable.insert(sha,obj_ref->size());
            }else{
                
            }
          }

        //Increment the window for next live bit search:
        curr_seg_index = liveBitInd+1;
      }

      curr_segment  = _livemap.next_live_segment(curr_segment);
  }

  log_info(gc,heap)("KOSTA:%d #of distinct obj in page,hs load factor:%d per ",distinctCount,hashTable.loadFactorPercent());

}

