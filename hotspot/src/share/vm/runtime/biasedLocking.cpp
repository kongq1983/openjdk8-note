/*
 * Copyright (c) 2005, 2014, Oracle and/or its affiliates. All rights reserved.
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

#include "precompiled.hpp"
#include "oops/klass.inline.hpp"
#include "oops/markOop.hpp"
#include "runtime/basicLock.hpp"
#include "runtime/biasedLocking.hpp"
#include "runtime/task.hpp"
#include "runtime/vframe.hpp"
#include "runtime/vmThread.hpp"
#include "runtime/vm_operations.hpp"

static bool _biased_locking_enabled = false;
BiasedLockingCounters BiasedLocking::_counters;

static GrowableArray<Handle>*  _preserved_oop_stack  = NULL;
static GrowableArray<markOop>* _preserved_mark_stack = NULL;

static void enable_biased_locking(Klass* k) {
  k->set_prototype_header(markOopDesc::biased_locking_prototype());
}

class VM_EnableBiasedLocking: public VM_Operation {
 private:
  bool _is_cheap_allocated;
 public:
  VM_EnableBiasedLocking(bool is_cheap_allocated) { _is_cheap_allocated = is_cheap_allocated; }
  VMOp_Type type() const          { return VMOp_EnableBiasedLocking; }
  Mode evaluation_mode() const    { return _is_cheap_allocated ? _async_safepoint : _safepoint; }
  bool is_cheap_allocated() const { return _is_cheap_allocated; }

  void doit() {
    // Iterate the system dictionary enabling biased locking for all
    // currently loaded classes
    SystemDictionary::classes_do(enable_biased_locking);
    // Indicate that future instances should enable it as well
    _biased_locking_enabled = true;

    if (TraceBiasedLocking) {
      tty->print_cr("Biased locking enabled");
    }
  }

  bool allow_nested_vm_operations() const        { return false; }
};


// One-shot PeriodicTask subclass for enabling biased locking
class EnableBiasedLockingTask : public PeriodicTask {
 public:
  EnableBiasedLockingTask(size_t interval_time) : PeriodicTask(interval_time) {}

  virtual void task() {
    // Use async VM operation to avoid blocking the Watcher thread.
    // VM Thread will free C heap storage.
    VM_EnableBiasedLocking *op = new VM_EnableBiasedLocking(true);
    VMThread::execute(op);

    // Reclaim our storage and disenroll ourself
    delete this;
  }
};

// todo 初始化，延迟偏向
void BiasedLocking::init() {
  // If biased locking is enabled, schedule a task to fire a few
  // seconds into the run which turns on biased locking for all
  // currently loaded classes as well as future ones. This is a
  // workaround for startup time regressions due to a large number of
  // safepoints being taken during VM startup for bias revocation.
  // Ideally we would have a lower cost for individual bias revocation
  // and not need a mechanism like this.
  if (UseBiasedLocking) { // 开启偏向锁
    if (BiasedLockingStartupDelay > 0) { // 延迟偏向时间
      EnableBiasedLockingTask* task = new EnableBiasedLockingTask(BiasedLockingStartupDelay);
      task->enroll();
    } else {
      VM_EnableBiasedLocking op(false);
      VMThread::execute(&op);
    }
  }
}


bool BiasedLocking::enabled() {
  return _biased_locking_enabled;
}

// Returns MonitorInfos for all objects locked on this thread in youngest to oldest order   line:210
static GrowableArray<MonitorInfo*>* get_or_compute_monitor_info(JavaThread* thread) { // // 线程还存活则遍历线程栈中所有的Lock Record
  GrowableArray<MonitorInfo*>* info = thread->cached_monitor_info(); // 当前线程缓存获取
  if (info != NULL) {
    return info;
  }
    // 在代码进入同步块的时候，如果同步对象锁状态为无锁状态（锁标志位为“01”状态，是否为偏向锁为“0”），
  info = new GrowableArray<MonitorInfo*>(); // 虚拟机首先将在当前线程的栈帧中建立一个名为锁记录（Lock Record）的空间，用于存储锁对象目前的Mark Word的拷贝，官方称之为 Displaced Mark Word。

  // It's possible for the thread to not have any Java frames on it,
  // i.e., if it's the main thread and it's already returned from main()
  if (thread->has_last_Java_frame()) {
    RegisterMap rm(thread);
    for (javaVFrame* vf = thread->last_java_vframe(&rm); vf != NULL; vf = vf->java_sender()) {
      GrowableArray<MonitorInfo*> *monitors = vf->monitors();
      if (monitors != NULL) {
        int len = monitors->length();
        // Walk monitors youngest to oldest
        for (int i = len - 1; i >= 0; i--) {
          MonitorInfo* mon_info = monitors->at(i);
          if (mon_info->eliminated()) continue;
          oop owner = mon_info->owner();
          if (owner != NULL) {
            info->append(mon_info);
          }
        }
      }
    }
  }

  thread->set_cached_monitor_info(info);
  return info;
}

// todo  611调用  偏向锁撤销  todo revoke_bias  611过来  allow_rebias=false   is_bulk=flase or true  批量撤销is_bulk=true
static BiasedLocking::Condition revoke_bias(oop obj, bool allow_rebias, bool is_bulk, JavaThread* requesting_thread) {
  markOop mark = obj->mark();
  if (!mark->has_bias_pattern()) {
    if (TraceBiasedLocking) {
      ResourceMark rm;
      tty->print_cr("  (Skipping revocation of object of type %s because it's no longer biased)",
                    obj->klass()->external_name()); //
    }
    return BiasedLocking::NOT_BIASED; // 没有偏向
  }
 // 到这里说明已偏向
  uint age = mark->age();
  markOop   biased_prototype = markOopDesc::biased_locking_prototype()->set_age(age); // 初始化偏向锁状态，并设置age
  markOop unbiased_prototype = markOopDesc::prototype()->set_age(age); // 无锁设置age

  if (TraceBiasedLocking && (Verbose || !is_bulk)) {
    ResourceMark rm;
    tty->print_cr("Revoking bias of object " INTPTR_FORMAT " , mark " INTPTR_FORMAT " , type %s , prototype header " INTPTR_FORMAT " , allow rebias %d , requesting thread " INTPTR_FORMAT,
                  p2i((void *)obj), (intptr_t) mark, obj->klass()->external_name(), (intptr_t) obj->klass()->prototype_header(), (allow_rebias ? 1 : 0), (intptr_t) requesting_thread);
  }

  JavaThread* biased_thread = mark->biased_locker(); // 有没有偏向锁持有线程
  if (biased_thread == NULL) { // 没有偏向线程 匿名偏向
    // Object is anonymously biased. We can get here if, for  匿名偏向。 我们可以到达这里，比如 我们撤销偏向是因为该对象生成了hashcode
    // example, we revoke the bias due to an identity hash code
    // being computed for an object.
    if (!allow_rebias) { // allow_rebias=false 撤销  不允许再偏向
      obj->set_mark(unbiased_prototype);  // 撤销偏向锁(恢复到无锁状态)
    }
    if (TraceBiasedLocking && (Verbose || !is_bulk)) {
      tty->print_cr("  Revoked bias of anonymously-biased object");
    }
    return BiasedLocking::BIAS_REVOKED; // 撤销
  }
    // 有偏向锁持有线程
  // Handle case where the thread toward which the object was biased has exited
  bool thread_is_alive = false;
  if (requesting_thread == biased_thread) { // 是同个线程，也就是当前线程就是偏向的线程
    thread_is_alive = true;
  } else {
    for (JavaThread* cur_thread = Threads::first(); cur_thread != NULL; cur_thread = cur_thread->next()) { // todo 遍历java线程
      if (cur_thread == biased_thread) {
        thread_is_alive = true;
        break;
      }
    }
  }
  if (!thread_is_alive) {  // 有偏向线程ID，但找不到持有偏向锁线程，偏向锁线程已经挂了
    if (allow_rebias) { // 再偏向
      obj->set_mark(biased_prototype);  //设置偏向状态
    } else {
      obj->set_mark(unbiased_prototype); // 设置无锁状态
    }
    if (TraceBiasedLocking && (Verbose || !is_bulk)) {
      tty->print_cr("  Revoked bias of object biased toward dead thread");
    }
    return BiasedLocking::BIAS_REVOKED;
  }

  // Thread owning bias is alive.  偏向线程活着
  // Check to see whether it currently owns the lock and, if so,  检查它当前线程是否拥有锁，如果是，
  // write down the needed displaced headers to the thread's stack.  将需要置换的displaced headers写入线程的堆栈
  // Otherwise, restore the object's header either to the unlocked 否则，将对象的头部恢复为未锁定的  或 无偏向状态
  // or unbiased state. // 线程还存活则遍历线程栈中所有的Lock Record
  GrowableArray<MonitorInfo*>* cached_monitor_info = get_or_compute_monitor_info(biased_thread); // line: 112
  BasicLock* highest_lock = NULL; //
  for (int i = 0; i < cached_monitor_info->length(); i++) { // 虚拟机首先将在当前线程的栈帧中建立一个名为锁记录（Lock Record）的空间，用于存储锁对象目前的Mark Word的拷贝，官方称之为 Displaced Mark Word
    MonitorInfo* mon_info = cached_monitor_info->at(i);  // MonitorInfo 在vframe.hpp:242   在代码进入同步块的时候，如果同步对象锁状态为无锁状态（锁标志位为“01”状态，是否为偏向锁为“0”）
    if (mon_info->owner() == obj) {  // 当前对象所持有  如果能找到对应的Lock Record说明偏向的线程还在执行同步代码块中的代码
      if (TraceBiasedLocking && Verbose) {
        tty->print_cr("   mon_info->owner (" PTR_FORMAT ") == obj (" PTR_FORMAT ")",
                      p2i((void *) mon_info->owner()),
                      p2i((void *) obj));
      }
      // Assume recursive case and fix up highest lock later 为了处理锁重入的case，在这里将Lock Record的Displaced Mark Word设置为null，第一个Lock Record会在下面的代码中再处理
      markOop mark = markOopDesc::encode((BasicLock*) NULL); //需要升级为轻量级锁，直接修改偏向线程栈中的Lock Record
      highest_lock = mon_info->lock(); // BasicLock* _lock
      highest_lock->set_displaced_header(mark); // 清空Lock Record
    } else {
      if (TraceBiasedLocking && Verbose) {
        tty->print_cr("   mon_info->owner (" PTR_FORMAT ") != obj (" PTR_FORMAT ")",
                      p2i((void *) mon_info->owner()),
                      p2i((void *) obj));
      }
    }
  }
  if (highest_lock != NULL) { // 修改第一个Lock Record为无锁状态，  轻量级锁的Lock Record
    // Fix up highest lock to contain displaced header and point
    // object at it
    highest_lock->set_displaced_header(unbiased_prototype); // 设置第一个Lock Record为无锁状态
    // Reset object header to point to displaced mark.
    // Must release storing the lock address for platforms without TSO
    // ordering (e.g. ppc).
    obj->release_set_mark(markOopDesc::encode(highest_lock)); // 然后将obj的mark word设置为指向该Lock Record的指针
    assert(!obj->mark()->has_bias_pattern(), "illegal mark state: stack lock used bias bit");
    if (TraceBiasedLocking && (Verbose || !is_bulk)) {
      tty->print_cr("  Revoked bias of currently-locked object");
    }
  } else { // 当前无锁
    if (TraceBiasedLocking && (Verbose || !is_bulk)) {
      tty->print_cr("  Revoked bias of currently-unlocked object");
    }
    if (allow_rebias) { // 允许偏向
      obj->set_mark(biased_prototype);
    } else {
      // Store the unlocked value into the object's header.
      obj->set_mark(unbiased_prototype); // 无锁
    }
  }

  return BiasedLocking::BIAS_REVOKED;
}


enum HeuristicsResult {
  HR_NOT_BIASED    = 1,
  HR_SINGLE_REVOKE = 2,
  HR_BULK_REBIAS   = 3, // 再偏向达到20次
  HR_BULK_REVOKE   = 4 // 偏向撤销达到40次 返回这个
};
// todo 偏向锁 import-import-import   591来调用
// todo 偏向锁次数  BiasedLockingBulkRebiasThreshold BiasedLockingBulkRevokeThreshold
static HeuristicsResult update_heuristics(oop o, bool allow_rebias) {
  markOop mark = o->mark();
  if (!mark->has_bias_pattern()) { // 没偏向
    return HR_NOT_BIASED;
  }

  // Heuristics to attempt to throttle the number of revocations. 尝试限制撤销次数的启发式方法。
  // Stages:
  // 1. Revoke the biases of all objects in the heap of this type,  撤销该类型堆中所有对象的biases
  //    but allow rebiasing of those objects if unlocked. 但如果解锁，则允许重新偏置这些对象
  // 2. Revoke the biases of all objects in the heap of this type 撤销该类型堆中所有对象的biases
  //    and don't allow rebiasing of these objects. Disable 并且不允许重新调整这些对象。 禁用分配该类型的对象并设置偏置位
  //    allocation of objects of that type with the bias bit set.
  Klass* k = o->klass();
  jlong cur_time = os::javaTimeMillis();
  jlong last_bulk_revocation_time = k->last_biased_lock_bulk_revocation_time(); //上次批量撤销时间
  int revocation_count = k->biased_lock_revocation_count(); // 偏置锁撤销次数
  if ((revocation_count >= BiasedLockingBulkRebiasThreshold) && // 20   [20,40)
      (revocation_count <  BiasedLockingBulkRevokeThreshold) && // 40
      (last_bulk_revocation_time != 0) &&  //上次批量撤销时间不等于0   BiasedLockingDecayTime=25000ms
      (cur_time - last_bulk_revocation_time >= BiasedLockingDecayTime)) { // 现在时间 - 上次批量撤销时间 >= 25000ms
    // This is the first revocation we've seen in a while of an
    // object of this type since the last time we performed a bulk
    // rebiasing operation. The application is allocating objects in
    // bulk which are biased toward a thread and then handing them
    // off to another thread. We can cope with this allocation
    // pattern via the bulk rebiasing mechanism so we reset the
    // klass's revocation count rather than allow it to increase
    // monotonically. If we see the need to perform another bulk
    // rebias operation later, we will, and if subsequently we see
    // many more revocation operations in a short period of time we
    // will completely disable biasing for this type.
    k->set_biased_lock_revocation_count(0);  // klass对象中偏置锁撤销次数清为0
    revocation_count = 0; // 偏置锁撤销次数清为0
  }

  // Make revocation count saturate just beyond BiasedLockingBulkRevokeThreshold
  if (revocation_count <= BiasedLockingBulkRevokeThreshold) { // 40
    revocation_count = k->atomic_incr_biased_lock_revocation_count(); // 次数+1
  }

  if (revocation_count == BiasedLockingBulkRevokeThreshold) { // 偏向撤销次数达到40次
    return HR_BULK_REVOKE;
  }

  if (revocation_count == BiasedLockingBulkRebiasThreshold) { // 重偏向达到20次
    return HR_BULK_REBIAS;
  }

  return HR_SINGLE_REVOKE;
}

// todo 批量撤销和批量重偏向  bulk_rebias=true(重偏向)
static BiasedLocking::Condition bulk_revoke_or_rebias_at_safepoint(oop o,
                                                                   bool bulk_rebias,
                                                                   bool attempt_rebias_of_object,
                                                                   JavaThread* requesting_thread) {
  assert(SafepointSynchronize::is_at_safepoint(), "must be done at safepoint");

  if (TraceBiasedLocking) {
    tty->print_cr("* Beginning bulk revocation (kind == %s) because of object "
                  INTPTR_FORMAT " , mark " INTPTR_FORMAT " , type %s",
                  (bulk_rebias ? "rebias" : "revoke"),
                  p2i((void *) o), (intptr_t) o->mark(), o->klass()->external_name());
  }

  jlong cur_time = os::javaTimeMillis();
  o->klass()->set_last_biased_lock_bulk_revocation_time(cur_time); // todo 设置时间


  Klass* k_o = o->klass();
  Klass* klass = k_o;

  if (bulk_rebias) { // 允许重偏向    HR_BULK_REBIAS
    // Use the epoch in the klass of the object to implicitly revoke
    // all biases of objects of this data type and force them to be
    // reacquired. However, we also need to walk the stacks of all
    // threads and update the headers of lightweight locked objects
    // with biases to have the current epoch.

    // If the prototype header doesn't have the bias pattern, don't
    // try to update the epoch -- assume another VM operation came in
    // and reset the header to the unbiased state, which will
    // implicitly cause all existing biases to be revoked
    if (klass->prototype_header()->has_bias_pattern()) {  // 已偏向
      int prev_epoch = klass->prototype_header()->bias_epoch();
      klass->set_prototype_header(klass->prototype_header()->incr_bias_epoch()); // 新的epoch incr_bias_epoch
      int cur_epoch = klass->prototype_header()->bias_epoch(); // 上面设置的 新的klass的epoch

      // Now walk all threads' stacks and adjust epochs of any biased // 现在遍历所有线程的堆栈并调整epochs of any biased
      // and locked objects of this data type we encounter // 和我们遇到的这种数据类型的锁定对象
      for (JavaThread* thr = Threads::first(); thr != NULL; thr = thr->next()) {
        GrowableArray<MonitorInfo*>* cached_monitor_info = get_or_compute_monitor_info(thr);
        for (int i = 0; i < cached_monitor_info->length(); i++) {
          MonitorInfo* mon_info = cached_monitor_info->at(i);
          oop owner = mon_info->owner();
          markOop mark = owner->mark();
          if ((owner->klass() == k_o) && mark->has_bias_pattern()) { // kclass要相等  java成面就是同个Class
            // We might have encountered this object already in the case of recursive locking
            assert(mark->bias_epoch() == prev_epoch || mark->bias_epoch() == cur_epoch, "error in bias epoch adjustment"); // 判断markword的epoch
            owner->set_mark(mark->set_bias_epoch(cur_epoch)); // 设置markword的epoch   (不同实例对象，同个Class场景)
          }
        }
      }
    }

    // At this point we're done. All we have to do is potentially
    // adjust the header of the given object to revoke its bias.
    revoke_bias(o, attempt_rebias_of_object && klass->prototype_header()->has_bias_pattern(), true, requesting_thread);
  } else {
    if (TraceBiasedLocking) {
      ResourceMark rm;
      tty->print_cr("* Disabling biased locking for type %s", klass->external_name());
    }
    // todo批量撤销
    // Disable biased locking for this data type. Not only will this   禁用偏向锁。这会导致对象不会偏向了
    // cause future instances to not be biased, but existing biased 已经存在的偏向锁对象，会通知，这些偏向会被撤销
    // instances will notice that this implicitly caused their biases
    // to be revoked.
    klass->set_prototype_header(markOopDesc::prototype());   // 轻量级锁

    // Now walk all threads' stacks and forcibly revoke the biases of
    // any locked and biased objects of this data type we encounter.
    for (JavaThread* thr = Threads::first(); thr != NULL; thr = thr->next()) {
      GrowableArray<MonitorInfo*>* cached_monitor_info = get_or_compute_monitor_info(thr);
      for (int i = 0; i < cached_monitor_info->length(); i++) {
        MonitorInfo* mon_info = cached_monitor_info->at(i);
        oop owner = mon_info->owner();
        markOop mark = owner->mark();
        if ((owner->klass() == k_o) && mark->has_bias_pattern()) {
          revoke_bias(owner, false, true, requesting_thread); // 撤销  // line:146
        }
      }
    }

    // Must force the bias of the passed object to be forcibly revoked  必须强制传递的对象的偏置被强行撤销
    // as well to ensure guarantees to callers 以及确保对调用者的保证
    revoke_bias(o, false, true, requesting_thread);  // line:146
  }

  if (TraceBiasedLocking) {
    tty->print_cr("* Ending bulk revocation");
  }

  BiasedLocking::Condition status_code = BiasedLocking::BIAS_REVOKED;

  if (attempt_rebias_of_object &&
      o->mark()->has_bias_pattern() &&
      klass->prototype_header()->has_bias_pattern()) {
    markOop new_mark = markOopDesc::encode(requesting_thread, o->mark()->age(),
                                           klass->prototype_header()->bias_epoch());
    o->set_mark(new_mark);
    status_code = BiasedLocking::BIAS_REVOKED_AND_REBIASED;
    if (TraceBiasedLocking) {
      tty->print_cr("  Rebiased object toward thread " INTPTR_FORMAT, (intptr_t) requesting_thread);
    }
  }

  assert(!o->mark()->has_bias_pattern() ||
         (attempt_rebias_of_object && (o->mark()->biased_locker() == requesting_thread)),
         "bug in bulk bias revocation");

  return status_code;
}


static void clean_up_cached_monitor_info() {
  // Walk the thread list clearing out the cached monitors
  for (JavaThread* thr = Threads::first(); thr != NULL; thr = thr->next()) {
    thr->set_cached_monitor_info(NULL);
  }
}


class VM_RevokeBias : public VM_Operation {
protected:
  Handle* _obj;
  GrowableArray<Handle>* _objs;
  JavaThread* _requesting_thread;
  BiasedLocking::Condition _status_code;

public:
  VM_RevokeBias(Handle* obj, JavaThread* requesting_thread)
    : _obj(obj)
    , _objs(NULL)
    , _requesting_thread(requesting_thread)
    , _status_code(BiasedLocking::NOT_BIASED) {}

  VM_RevokeBias(GrowableArray<Handle>* objs, JavaThread* requesting_thread)
    : _obj(NULL)
    , _objs(objs)
    , _requesting_thread(requesting_thread)
    , _status_code(BiasedLocking::NOT_BIASED) {}

  virtual VMOp_Type type() const { return VMOp_RevokeBias; }

  virtual bool doit_prologue() {
    // Verify that there is actual work to do since the callers just
    // give us locked object(s). If we don't find any biased objects
    // there is nothing to do and we avoid a safepoint.
    if (_obj != NULL) {
      markOop mark = (*_obj)()->mark();
      if (mark->has_bias_pattern()) {
        return true;
      }
    } else {
      for ( int i = 0 ; i < _objs->length(); i++ ) {
        markOop mark = (_objs->at(i))()->mark();
        if (mark->has_bias_pattern()) {
          return true;
        }
      }
    }
    return false;
  }

  virtual void doit() {
    if (_obj != NULL) {
      if (TraceBiasedLocking) {
        tty->print_cr("Revoking bias with potentially per-thread safepoint:");
      }
      _status_code = revoke_bias((*_obj)(), false, false, _requesting_thread);
      clean_up_cached_monitor_info();
      return;
    } else {
      if (TraceBiasedLocking) {
        tty->print_cr("Revoking bias with global safepoint:");
      }
      BiasedLocking::revoke_at_safepoint(_objs);
    }
  }

  BiasedLocking::Condition status_code() const {
    return _status_code;
  }
};


class VM_BulkRevokeBias : public VM_RevokeBias {
private:
  bool _bulk_rebias;
  bool _attempt_rebias_of_object;

public:
  VM_BulkRevokeBias(Handle* obj, JavaThread* requesting_thread,
                    bool bulk_rebias,
                    bool attempt_rebias_of_object)
    : VM_RevokeBias(obj, requesting_thread)
    , _bulk_rebias(bulk_rebias)
    , _attempt_rebias_of_object(attempt_rebias_of_object) {}

  virtual VMOp_Type type() const { return VMOp_BulkRevokeBias; }
  virtual bool doit_prologue()   { return true; }

  virtual void doit() {
    _status_code = bulk_revoke_or_rebias_at_safepoint((*_obj)(), _bulk_rebias, _attempt_rebias_of_object, _requesting_thread);
    clean_up_cached_monitor_info();
  }
};
// 如果不是返回BIAS_REVOKED_AND_REBIASED  要去slow_enter，相当于变轻量级锁
// todo 获取偏向锁  BIAS_REVOKED:撤销  重量级锁 -> 无锁  轻量级锁 -> 无锁  详见markOop.hpp
BiasedLocking::Condition BiasedLocking::revoke_and_rebias(Handle obj, bool attempt_rebias, TRAPS) { // attempt_rebias=true(继续偏向)  attempt_rebias=false(撤销偏向)
  assert(!SafepointSynchronize::is_at_safepoint(), "must not be called while at safepoint"); //必须在安全点

  // We can revoke the biases of anonymously-biased objects
  // efficiently enough that we should not cause these revocations to
  // update the heuristics because doing so may cause unwanted bulk
  // revocations (which are expensive) to occur.
  markOop mark = obj->mark(); //2：读取对象头 markOop.hpp
  if (mark->is_biased_anonymously() && !attempt_rebias) { // 3:没有线程获取了偏向锁(标志位是偏向锁  但没有设置特定线程)
    // We are probably trying to revoke the bias of this object due to
    // an identity hash code computation. Try to revoke the bias
    // without a safepoint. This is possible if we can successfully
    // compare-and-exchange an unbiased header into the mark word of
    // the object, meaning that no other thread has raced to acquire
    // the bias of the object.
    markOop biased_value       = mark;
    markOop unbiased_prototype = markOopDesc::prototype()->set_age(mark->age()); // 无锁
    markOop res_mark = (markOop) Atomic::cmpxchg_ptr(unbiased_prototype, obj->mark_addr(), mark);
    if (res_mark == biased_value) { // biased_value=mark 也就是cas成功  *****偏向锁 -> 无锁
      return BIAS_REVOKED; // 如果之前的和现在的一样，说明撤销成功，BIAS_REVOKED本身是一个枚举
    }
  } else if (mark->has_bias_pattern()) { //4:已经偏向了 标志位=0101 这里没说被当前线程偏向
    Klass* k = obj->klass();
    markOop prototype_header = k->prototype_header();
    if (!prototype_header->has_bias_pattern()) { // kclass不是偏向锁标志
      // This object has a stale bias from before the bulk revocation
      // for this data type occurred. It's pointless to update the
      // heuristics at this point so simply update the header with a
      // CAS. If we fail this race, the object's bias has been revoked  如果本次cas失败，那让别的线程撤销偏向
      // by another thread so we simply return and let the caller deal  所以我们简单地返回，并让调用者处理用它。
      // with it.
      markOop biased_value       = mark;
      markOop res_mark = (markOop) Atomic::cmpxchg_ptr(prototype_header, obj->mark_addr(), mark);
      assert(!(*(obj->mark_addr()))->has_bias_pattern(), "even if we raced, should still be revoked"); // 如果成功 撤销obj的偏向锁
      return BIAS_REVOKED; // 当线程想要获取偏向锁时，对比当前对象的epoch值与Klass里的epoch值，发现不相等，则认为过期
    } else if (prototype_header->bias_epoch() != mark->bias_epoch()) { //详见markOop.hpp   obj.epoch!=kclass.epoch
      // The epoch of this biasing has expired indicating that the
      // object is effectively unbiased. Depending on whether we need
      // to rebias or revoke the bias of this object we can do it
      // efficiently enough with a CAS that we shouldn't update the
      // heuristics. This is normally done in the assembly code but we
      // can reach this point due to various points in the runtime
      // needing to revoke biases.
      if (attempt_rebias) { // attempt_rebias=true 获取
        assert(THREAD->is_Java_thread(), "");
        markOop biased_value       = mark; // 54bit threadId | epoch 2bit | unused 1bit | age 4bit | 1 biased 1bit | 01 2bit lock
        markOop rebiased_prototype = markOopDesc::encode((JavaThread*) THREAD, mark->age(), prototype_header->bias_epoch()); // 设置偏向线程
        markOop res_mark = (markOop) Atomic::cmpxchg_ptr(rebiased_prototype, obj->mark_addr(), mark); // 注意这里是obj 是实例对象，也就是同个对象只能有1个成功
        if (res_mark == biased_value) { //  markOop* mark_addr() const    { return (markOop*) &_mark; }
          return BIAS_REVOKED_AND_REBIASED; // *********成功获取偏向锁
        }
      } else { // 撤销   markOopDesc::prototype() = markOop( no_hash_in_place | no_lock_in_place )
        markOop biased_value       = mark; // unused 25bit | hashcode 31bit | unused 1bit | age 4bit | 0 biased 1bit | 01 2bit lock
        markOop unbiased_prototype = markOopDesc::prototype()->set_age(mark->age()); // 因为偏向锁不可能有hashcode 这里设置age
        markOop res_mark = (markOop) Atomic::cmpxchg_ptr(unbiased_prototype, obj->mark_addr(), mark);
        if (res_mark == biased_value) {
          return BIAS_REVOKED; // 撤销成功
        }
      }
    }
  }
  //5:没有执行偏向，通过启发式的方式决定到底是执行撤销还是执行rebias  todo 启发式偏向
  HeuristicsResult heuristics = update_heuristics(obj(), attempt_rebias);  // todo 偏向锁 import-import-impport
  if (heuristics == HR_NOT_BIASED) {
    return NOT_BIASED; //没有偏向
  } else if (heuristics == HR_SINGLE_REVOKE) {
    Klass *k = obj->klass(); //5.2:启发式决定执行单次的撤销
    markOop prototype_header = k->prototype_header();
    if (mark->biased_locker() == THREAD &&
        prototype_header->bias_epoch() == mark->bias_epoch()) {
      // A thread is trying to revoke the bias of an object biased
      // toward it, again likely due to an identity hash code
      // computation. We can again avoid a safepoint in this case
      // since we are only going to walk our own stack. There are no
      // races with revocations occurring in other threads because we
      // reach no safepoints in the revocation path.
      // Also check the epoch because even if threads match, another thread
      // can come in with a CAS to steal the bias of an object that has a
      // stale epoch.
      ResourceMark rm;
      if (TraceBiasedLocking) {
        tty->print_cr("Revoking bias by walking my own stack:");
      } // revoke_bias:146
      BiasedLocking::Condition cond = revoke_bias(obj(), false, false, (JavaThread*) THREAD);
      ((JavaThread*) THREAD)->set_cached_monitor_info(NULL);
      assert(cond == BIAS_REVOKED, "why not?");
      return cond;
    } else { // HR_BULK_REVOKE  HR_BULK_REBIAS
      VM_RevokeBias revoke(&obj, (JavaThread*) THREAD);
      VMThread::execute(&revoke);
      return revoke.status_code();
    }
  }

  assert((heuristics == HR_BULK_REVOKE) ||
         (heuristics == HR_BULK_REBIAS), "?");
  // 6：等到虚拟机运行到safepoint,实际就是执行  VM_BulkRevokeBias 的doit的 bulk_revoke_or_rebias_at_safepoint方法
  VM_BulkRevokeBias bulk_revoke(&obj, (JavaThread*) THREAD,
                                (heuristics == HR_BULK_REBIAS),
                                attempt_rebias);
  VMThread::execute(&bulk_revoke);
  return bulk_revoke.status_code();
}


void BiasedLocking::revoke(GrowableArray<Handle>* objs) {
  assert(!SafepointSynchronize::is_at_safepoint(), "must not be called while at safepoint");
  if (objs->length() == 0) {
    return;
  }
  VM_RevokeBias revoke(objs, JavaThread::current());
  VMThread::execute(&revoke);
}


void BiasedLocking::revoke_at_safepoint(Handle h_obj) {
  assert(SafepointSynchronize::is_at_safepoint(), "must only be called while at safepoint");
  oop obj = h_obj();
  HeuristicsResult heuristics = update_heuristics(obj, false);
  if (heuristics == HR_SINGLE_REVOKE) {
    revoke_bias(obj, false, false, NULL);
  } else if ((heuristics == HR_BULK_REBIAS) ||
             (heuristics == HR_BULK_REVOKE)) {
    bulk_revoke_or_rebias_at_safepoint(obj, (heuristics == HR_BULK_REBIAS), false, NULL); // HR_BULK_REBIAS=再偏向达到20次
  }
  clean_up_cached_monitor_info();
}


void BiasedLocking::revoke_at_safepoint(GrowableArray<Handle>* objs) {
  assert(SafepointSynchronize::is_at_safepoint(), "must only be called while at safepoint");
  int len = objs->length();
  for (int i = 0; i < len; i++) {
    oop obj = (objs->at(i))();
    HeuristicsResult heuristics = update_heuristics(obj, false);
    if (heuristics == HR_SINGLE_REVOKE) {
      revoke_bias(obj, false, false, NULL);
    } else if ((heuristics == HR_BULK_REBIAS) || // HR_BULK_REBIAS = 重偏向达到20次
               (heuristics == HR_BULK_REVOKE)) { // HR_BULK_REVOKE = 偏向撤销次数达到40次
      bulk_revoke_or_rebias_at_safepoint(obj, (heuristics == HR_BULK_REBIAS), false, NULL); // line 321  HR_BULK_REBIAS=再偏向达到20次
    }
  }
  clean_up_cached_monitor_info();
}


void BiasedLocking::preserve_marks() {
  if (!UseBiasedLocking)
    return;

  assert(SafepointSynchronize::is_at_safepoint(), "must only be called while at safepoint");

  assert(_preserved_oop_stack  == NULL, "double initialization");
  assert(_preserved_mark_stack == NULL, "double initialization");

  // In order to reduce the number of mark words preserved during GC
  // due to the presence of biased locking, we reinitialize most mark
  // words to the class's prototype during GC -- even those which have
  // a currently valid bias owner. One important situation where we
  // must not clobber a bias is when a biased object is currently
  // locked. To handle this case we iterate over the currently-locked
  // monitors in a prepass and, if they are biased, preserve their
  // mark words here. This should be a relatively small set of objects
  // especially compared to the number of objects in the heap.
  _preserved_mark_stack = new (ResourceObj::C_HEAP, mtInternal) GrowableArray<markOop>(10, true);
  _preserved_oop_stack = new (ResourceObj::C_HEAP, mtInternal) GrowableArray<Handle>(10, true);

  ResourceMark rm;
  Thread* cur = Thread::current();
  for (JavaThread* thread = Threads::first(); thread != NULL; thread = thread->next()) {
    if (thread->has_last_Java_frame()) {
      RegisterMap rm(thread);
      for (javaVFrame* vf = thread->last_java_vframe(&rm); vf != NULL; vf = vf->java_sender()) {
        GrowableArray<MonitorInfo*> *monitors = vf->monitors();
        if (monitors != NULL) {
          int len = monitors->length();
          // Walk monitors youngest to oldest
          for (int i = len - 1; i >= 0; i--) {
            MonitorInfo* mon_info = monitors->at(i);
            if (mon_info->owner_is_scalar_replaced()) continue;
            oop owner = mon_info->owner();
            if (owner != NULL) {
              markOop mark = owner->mark();
              if (mark->has_bias_pattern()) {
                _preserved_oop_stack->push(Handle(cur, owner));
                _preserved_mark_stack->push(mark);
              }
            }
          }
        }
      }
    }
  }
}


void BiasedLocking::restore_marks() {
  if (!UseBiasedLocking)
    return;

  assert(_preserved_oop_stack  != NULL, "double free");
  assert(_preserved_mark_stack != NULL, "double free");

  int len = _preserved_oop_stack->length();
  for (int i = 0; i < len; i++) {
    Handle owner = _preserved_oop_stack->at(i);
    markOop mark = _preserved_mark_stack->at(i);
    owner->set_mark(mark);
  }

  delete _preserved_oop_stack;
  _preserved_oop_stack = NULL;
  delete _preserved_mark_stack;
  _preserved_mark_stack = NULL;
}


int* BiasedLocking::total_entry_count_addr()                   { return _counters.total_entry_count_addr(); }
int* BiasedLocking::biased_lock_entry_count_addr()             { return _counters.biased_lock_entry_count_addr(); }
int* BiasedLocking::anonymously_biased_lock_entry_count_addr() { return _counters.anonymously_biased_lock_entry_count_addr(); }
int* BiasedLocking::rebiased_lock_entry_count_addr()           { return _counters.rebiased_lock_entry_count_addr(); }
int* BiasedLocking::revoked_lock_entry_count_addr()            { return _counters.revoked_lock_entry_count_addr(); }
int* BiasedLocking::fast_path_entry_count_addr()               { return _counters.fast_path_entry_count_addr(); }
int* BiasedLocking::slow_path_entry_count_addr()               { return _counters.slow_path_entry_count_addr(); }


// BiasedLockingCounters

int BiasedLockingCounters::slow_path_entry_count() {
  if (_slow_path_entry_count != 0) {
    return _slow_path_entry_count;
  }
  int sum = _biased_lock_entry_count   + _anonymously_biased_lock_entry_count +
            _rebiased_lock_entry_count + _revoked_lock_entry_count +
            _fast_path_entry_count;

  return _total_entry_count - sum;
}

void BiasedLockingCounters::print_on(outputStream* st) {
  tty->print_cr("# total entries: %d", _total_entry_count);
  tty->print_cr("# biased lock entries: %d", _biased_lock_entry_count);
  tty->print_cr("# anonymously biased lock entries: %d", _anonymously_biased_lock_entry_count);
  tty->print_cr("# rebiased lock entries: %d", _rebiased_lock_entry_count);
  tty->print_cr("# revoked lock entries: %d", _revoked_lock_entry_count);
  tty->print_cr("# fast path lock entries: %d", _fast_path_entry_count);
  tty->print_cr("# slow path lock entries: %d", slow_path_entry_count());
}
