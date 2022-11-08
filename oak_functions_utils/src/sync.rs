//
// Copyright 2022 The Project Oak Authors
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

use core::{
    cell::UnsafeCell,
    hint::spin_loop,
    mem::MaybeUninit,
    sync::atomic::{AtomicBool, Ordering},
};
use lock_api::{GuardSend, RawMutex};
use spinning_top::{const_spinlock, Spinlock};

/// A synchronised implementation of a cell that can be initialized only once.
///
/// This achieves the same goal as `std::sync::OnceLock`, but uses a spinlock to be compatible with
/// `no_std`.
pub struct OnceCell<T> {
    initialized: AtomicBool,
    lock: Spinlock<()>,
    value: UnsafeCell<MaybeUninit<T>>,
}

impl<T> OnceCell<T> {
    pub const fn new() -> Self {
        Self {
            initialized: AtomicBool::new(false),
            lock: const_spinlock(()),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    pub fn get(&self) -> Option<&T> {
        if !self.initialized.load(Ordering::Acquire) {
            return None;
        }
        // Safety: there are no mutable references to the inner value if `initialized` is set to
        // `true`, and the value has been initialized, so it is safe to create a new shared
        // reference and assume it is initialized.
        Some(unsafe { (*self.value.get()).assume_init_ref() })
    }

    pub fn set(&self, value: T) -> Result<(), T> {
        // Do an initial check to see whether the value has been initialized.
        if !self.initialized.load(Ordering::Acquire) {
            // Lock to make sure we have exclusive access.
            let _lock = self.lock.lock();
            // Double check that someone else didn't initialize while we were waiting to get the
            // lock. Relaxed ordering is sufficient since the lock acts as a memory barrier and also
            // ensures no concurrent access to the code that stores the value.
            if !self.initialized.load(Ordering::Relaxed) {
                // Safety: the combination of the lock and the fact that `initialized` is `false`
                // ensures that we have exclusive access to the inner value, so taking a mutable
                // reference to it is safe.
                unsafe { &mut *self.value.get() }.write(value);
                self.initialized.store(true, Ordering::Release);
                return Ok(());
            }
        }
        Err(value)
    }
}

pub struct SpinLock(AtomicBool);

unsafe impl RawMutex for SpinLock {
    type GuardMarker = GuardSend;

    // This should be replaced in the future by `const fn new() -> Self`.
    #[allow(clippy::declare_interior_mutable_const)]
    const INIT: SpinLock = SpinLock(AtomicBool::new(false));

    fn lock(&self) {
        while self
            .0
            .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            // While spinning to acquire the lock, we should perform a read.
            while self.0.load(Ordering::Relaxed) {
                spin_loop()
            }
        }
    }

    fn try_lock(&self) -> bool {
        self.0
            .compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    unsafe fn unlock(&self) {
        self.0.store(false, Ordering::Release);
    }
}

pub type Mutex<T> = lock_api::Mutex<SpinLock, T>;
pub type MutexGuard<'a, T> = lock_api::MutexGuard<'a, SpinLock, T>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_once_cell_get_uninitialized() {
        let cell = OnceCell::<u64>::new();
        assert!(cell.get().is_none());
    }

    #[test]
    fn test_once_cell_set_and_get() {
        let cell = OnceCell::<u64>::new();
        assert!(cell.get().is_none());
        assert!(cell.set(4).is_ok());
        assert_eq!(cell.get(), Some(&4));
    }

    #[test]
    fn test_once_cell_set_twice() {
        let cell = OnceCell::<u64>::new();
        assert!(cell.set(4).is_ok());
        assert_eq!(cell.set(5), Err(5));
        assert_eq!(cell.get(), Some(&4));
    }
}
