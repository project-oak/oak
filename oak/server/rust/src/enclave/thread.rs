use alloc::boxed::Box;

use core::any::Any;
use core::result;
use core::cmp;
use core::ffi;
use core::mem;
use core::ops::Fn;
use core::ptr;

use super::io;

// use po::*;

// Based on
// - rust/src/libstd/sys_common/thread.rs
// - rust/src/libstd/sys/unix/thread.rs
// Major differences:
// - No configuration loading from env
// - No stack guards
// - Doesn't set stack size (unsupported by Asylo)

use core::sync::atomic::{self, Ordering};

pub const DEFAULT_MIN_STACK_SIZE: usize = 1024 * 1024;

#[allow(dead_code)]
pub unsafe fn start_thread(main: *mut u8) {
    // Next, set up our stack overflow handler which may get triggered if we run
    // out of stack.
    // TODO: FIXME: needed for oak ?
    // let _handler = stack_overflow::Handler::new();

    // Finally, let's run some code.
    Box::from_raw(main as *mut Box<dyn FnOnce()>)()
}

pub fn min_stack() -> usize {
    static MIN: atomic::AtomicUsize = atomic::AtomicUsize::new(0);
    match MIN.load(Ordering::SeqCst) {
        0 => {}
        n => return n - 1,
    }
    let amt = DEFAULT_MIN_STACK_SIZE;

    // 0 is our sentinel value, so ensure that we'll never see 0 after
    // initialization has run
    MIN.store(amt + 1, Ordering::SeqCst);
    amt
}

pub struct Thread {
    id: libc::pthread_t,
}

unsafe impl Send for Thread {}
unsafe impl Sync for Thread {}

impl Thread {
    // unsafe: see thread::Builder::spawn_unchecked for safety requirements
    pub unsafe fn new(p: Box<dyn FnOnce()>) -> io::Result<Thread> {
    // pub unsafe fn new(stack: usize, p: Box<dyn FnOnce()>) -> io::Result<Thread> {
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

    //TODO: Duration
    // pub fn sleep(dur: Duration) {
    //     let mut secs = dur.as_secs();
    //     let mut nsecs = dur.subsec_nanos() as _;

    //     // If we're awoken with a signal then the return value will be -1 and
    //     // nanosleep will fill in `ts` with the remaining time.
    //     unsafe {
    //         while secs > 0 || nsecs > 0 {
    //             let mut ts = libc::timespec {
    //                 tv_sec: cmp::min(libc::time_t::max_value() as u64, secs) as libc::time_t,
    //                 tv_nsec: nsecs,
    //             };
    //             secs -= ts.tv_sec as u64;
    //             if libc::nanosleep(&ts, &mut ts) == -1 {
    //                 assert_eq!(os::errno(), libc::EINTR);
    //                 secs += ts.tv_sec as u64;
    //                 nsecs = ts.tv_nsec;
    //             } else {
    //                 nsecs = 0;
    //             }
    //         }
    //     }
    // }

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

fn min_stack_size(_: *const libc::pthread_attr_t) -> usize {
    libc::PTHREAD_STACK_MIN
}
