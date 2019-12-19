#![allow(dead_code)] // stack_guard isn't used right now on all platforms

use crate::core::cell::RefCell;
use crate::thread::Thread;

struct ThreadInfo {
    thread: Thread,
}

// thread_local! { static THREAD_INFO: RefCell<Option<ThreadInfo>> = RefCell::new(None) }

 A
$(#[$attr])* $vis const $name: $crate::thread::LocalKey<THRAD_INFO> = {
      #[inline]
      fn __init() -> THREAD_INFO { $init }

      unsafe fn __getit() -> $crate::option::Option<&'static THREAD_INFO> {
        #[cfg(all(target_arch = "wasm32", not(target_feature = "atomics")))]
        static __KEY: $crate::thread::__StaticLocalKeyInner<THREAD_INFO> =
          $crate::thread::__StaticLocalKeyInner::new();

           #[thread_local]
           #[cfg(all(
               target_thread_local,
               not(all(target_arch = "wasm32", not(target_feature = "atomics"))),
           ))]
           static __KEY: $crate::thread::__FastLocalKeyInner<THREAD_INFO> =
               $crate::thread::__FastLocalKeyInner::new();

           #[cfg(all(
               not(target_thread_local),
               not(all(target_arch = "wasm32", not(target_feature = "atomics"))),
           ))]
           static __KEY: $crate::thread::__OsLocalKeyInner<THREAD_INFO> =
               $crate::thread::__OsLocalKeyInner::new();

           __KEY.get(__init)
        }

        unsafe {
          $crate::thread::LocalKey::new(__getit)
        }
    };

impl ThreadInfo {
    fn with<R, F>(f: F) -> Option<R>
    where
        F: FnOnce(&mut ThreadInfo) -> R,
    {
        THREAD_INFO
            .try_with(move |c| {
                if c.borrow().is_none() {
                    *c.borrow_mut() =
                        Some(ThreadInfo { thread: Thread::new(None) })
                }
                f(c.borrow_mut().as_mut().unwrap())
            })
            .ok()
    }
}

pub fn current_thread() -> Option<Thread> {
    ThreadInfo::with(|info| info.thread.clone())
}

pub fn set(thread: Thread) {
    THREAD_INFO.with(|c| assert!(c.borrow().is_none()));
    THREAD_INFO.with(move |c| *c.borrow_mut() = Some(ThreadInfo { thread }));
}
