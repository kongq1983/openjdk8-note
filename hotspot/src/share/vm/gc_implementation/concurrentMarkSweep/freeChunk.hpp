/*
 * Copyright (c) 2001, 2012, Oracle and/or its affiliates. All rights reserved.
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
 *
 */

#ifndef SHARE_VM_GC_IMPLEMENTATION_CONCURRENTMARKSWEEP_FREECHUNK_HPP
#define SHARE_VM_GC_IMPLEMENTATION_CONCURRENTMARKSWEEP_FREECHUNK_HPP

#include "memory/allocation.hpp"
#include "memory/memRegion.hpp"
#include "oops/markOop.hpp"
#include "runtime/mutex.hpp"
#include "utilities/debug.hpp"
#include "utilities/globalDefinitions.hpp"
#include "utilities/ostream.hpp"

//
// Free block maintenance for Concurrent Mark Sweep Generation
//
// The main data structure for free blocks are
// . an indexed array of small free blocks, and
// . a dictionary of large free blocks
//

// No virtuals in FreeChunk (don't want any vtables).

// A FreeChunk is merely a chunk that can be in a doubly linked list
// and has a size field. NOTE: FreeChunks are distinguished from allocated
// objects in two ways (by the sweeper), depending on whether the VM is 32 or
// 64 bits.
// In 32 bits or 64 bits without CompressedOops, the second word (prev) has the
// LSB set to indicate a free chunk; allocated objects' klass() pointers
// don't have their LSB set. The corresponding bit in the CMSBitMap is
// set when the chunk is allocated. There are also blocks that "look free"
// but are not part of the free list and should not be coalesced into larger
// free blocks. These free blocks have their two LSB's set.
// FreeChunk也是位于老年代的堆内存中，怎么跟正常的Java对象区分了？如果是32位或者64位下不开启UseCompressedOops则通过prev字段的地址最后一位来标识，如果是64位下开启UseCompressedOops则通过size字段来标识
class FreeChunk VALUE_OBJ_CLASS_SPEC {
  friend class VMStructs;
  // For 64 bit compressed oops, the markOop encodes both the size and the
  // indication that this is a FreeChunk and not an object.
  volatile size_t   _size; // 如果是64位下开启UseCompressedOops则通过size字段来标识
  FreeChunk* _prev; // 如果是32位或者64位下不开启UseCompressedOops则通过prev字段的地址最后一位来标识
  FreeChunk* _next;

  markOop mark()     const volatile { return (markOop)_size; }
  void set_mark(markOop m)          { _size = (size_t)m; }

 public:
  NOT_PRODUCT(static const size_t header_size();)

  // Returns "true" if the address indicates that the block represents
  // a free chunk. //根据addr判断这是否是一个FreeChunk，如果是返回true
  static bool indicatesFreeChunk(const HeapWord* addr) {
    // Force volatile read from addr because value might change between
    // calls.  We really want the read of _mark and _prev from this pointer
    // to be volatile but making the fields volatile causes all sorts of
    // compilation errors.
    return ((volatile FreeChunk*)addr)->is_free();
  }

  bool is_free() const volatile {
    LP64_ONLY(if (UseCompressedOops) return mark()->is_cms_free_chunk(); else)
    return (((intptr_t)_prev) & 0x1) == 0x1;
  }
  bool cantCoalesce() const {
    assert(is_free(), "can't get coalesce bit on not free");
    return (((intptr_t)_prev) & 0x2) == 0x2;
  }
  void dontCoalesce() { //dontCoalesce用于标记当前FreeChunk不支持合并成一个更大的FreeChunk
    // the block should be free
    assert(is_free(), "Should look like a free block");
    _prev = (FreeChunk*)(((intptr_t)_prev) | 0x2); //| 0x2将prev地址的倒数第二位置为1
  } // 第二个字宽，_metadata对应于_prev。在64位下开启指针压缩的条件下，都读取第一个字宽的数据，在32位或者64位下不开启指针压缩时都读取第二个字宽的数据，然后根据特殊的位来判断是否是FreeChunk
  FreeChunk* prev() const { //& ~(0x3)实际就是把ptr地址的最后两位换成0，最后一位表示是否是FreeChunk，倒数第二位用于表示该FreeChunk不能执行合并
    return (FreeChunk*)(((intptr_t)_prev) & ~(0x3));
  }

  debug_only(void* prev_addr() const { return (void*)&_prev; })
  debug_only(void* next_addr() const { return (void*)&_next; })
  debug_only(void* size_addr() const { return (void*)&_size; })

  size_t size() const volatile { //size属性的读写
    LP64_ONLY(if (UseCompressedOops) return mark()->get_size(); else )
    return _size;
  }
  void set_size(size_t sz) {
    LP64_ONLY(if (UseCompressedOops) set_mark(markOopDesc::set_size_and_free(sz)); else )
    _size = sz;
  }

  FreeChunk* next()   const { return _next; }

  void link_after(FreeChunk* ptr) {
    link_next(ptr);
    if (ptr != NULL) ptr->link_prev(this);
  }
  void link_next(FreeChunk* ptr) { _next = ptr; }
  void link_prev(FreeChunk* ptr) { //prev属性的读写，|0x1就是将ptr地址的最后一位变成1，ptr因为需要按照内存页对齐，所以ptr通常最后的N位都是0，N位取决于内存页的大小
    LP64_ONLY(if (UseCompressedOops) _prev = ptr; else)
    _prev = (FreeChunk*)((intptr_t)ptr | 0x1);
  }
  void clear_next()              { _next = NULL; }
  void markNotFree() { //将FreeChunk标记为非Free
    // Set _prev (klass) to null before (if) clearing the mark word below
    _prev = NULL;
#ifdef _LP64
    if (UseCompressedOops) {
      OrderAccess::storestore();
      set_mark(markOopDesc::prototype());
    }
#endif
    assert(!is_free(), "Error");
  }

  // Return the address past the end of this chunk
  uintptr_t* end() const { return ((uintptr_t*) this) + size(); }

  // debugging
  void verify()             const PRODUCT_RETURN;
  void verifyList()         const PRODUCT_RETURN;
  void mangleAllocated(size_t size) PRODUCT_RETURN;
  void mangleFreed(size_t size)     PRODUCT_RETURN;

  void print_on(outputStream* st);
};

extern size_t MinChunkSize;


#endif // SHARE_VM_GC_IMPLEMENTATION_CONCURRENTMARKSWEEP_FREECHUNK_HPP
