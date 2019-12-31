//
// Copyright 2019 The Project Oak Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

// Based on
// - https://github.com/rust-lang/rust/blob/6b561b4917e803c4be4ca44d8e552b680cb9e380/src/libstd/sys_common/thread.rs
// - https://github.com/rust-lang/rust/blob/6b561b4917e803c4be4ca44d8e552b680cb9e380/src/libstd/sys/unix/thread.rs
// Major differences:
// - No configuration loading from env
// - No stack guards
// - Doesn't set stack size (unsupported by Asylo)
// - No sleep functionality. Should we re-add, does it make sense to have sleep which depends on
// untrusted time

use alloc::boxed::Box;

use core::mem;
use core::ptr;

use crate::common::io;

#[allow(dead_code)]
pub unsafe fn start_thread(main: *mut u8) {
    // TODO: FIXME: needed for oak ?
    //
    // XXX original comment:
    // Next, set up our stack overflow handler which may get triggered if we run
    // out of stack.
    // XXX asylo doesn't provide the functions needed to set this up

    Box::from_raw(main as *mut Box<dyn FnOnce()>)()
}

pub struct Thread {
    id: libc::pthread_t,
}

unsafe impl Send for Thread {}
unsafe impl Sync for Thread {}

impl Thread {
    // unsafe: see thread::Builder::spawn_unchecked for safety requirements
    pub unsafe fn new(p: Box<dyn FnOnce()>) -> io::Result<Thread> {
        let p = box p;
        let mut native: libc::pthread_t = mem::zeroed();
        let mut attr: libc::pthread_attr_t = mem::zeroed();
        assert_eq!(libc::pthread_attr_init(&mut attr), 0);

        let ret = libc::pthread_create(&mut native, &attr, thread_start, &*p as *const _ as *mut _);
        assert_eq!(libc::pthread_attr_destroy(&mut attr), 0);

        return if ret != 0 {
            Err(io::Error::from_raw_os_error(ret))
        } else {
            mem::forget(p); // ownership passed to pthread_create
            Ok(Thread { id: native })
        };

        extern "C" fn thread_start(main: *mut libc::c_void) -> *mut libc::c_void {
            unsafe {
                start_thread(main as *mut u8);
            }
            ptr::null_mut()
        }
    }

    pub fn yield_now() {
        let ret = unsafe { libc::sched_yield() };
        debug_assert_eq!(ret, 0);
    }

    pub fn join(self) {
        unsafe {
            let ret = libc::pthread_join(self.id, ptr::null_mut());
            mem::forget(self);
            assert!(ret == 0, "failed to join thread: {}", io::Error::from_raw_os_error(ret));
        }
    }

    pub fn id(&self) -> libc::pthread_t {
        self.id
    }

    pub fn into_id(self) -> libc::pthread_t {
        let id = self.id;
        mem::forget(self);
        id
    }
}

impl Drop for Thread {
    fn drop(&mut self) {
        let ret = unsafe { libc::pthread_detach(self.id) };
        debug_assert_eq!(ret, 0);
    }
}
