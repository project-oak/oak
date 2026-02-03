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

//! Synchronization utils.

use core::{
    cell::UnsafeCell,
    mem::MaybeUninit,
    sync::atomic::{AtomicBool, Ordering},
};

use spinning_top::Spinlock;

/// A synchronised implementation of a cell that can be initialized only once.
///
/// This achieves the same goal as `std::sync::OnceLock`, but uses a spinlock to
/// be compatible with `no_std`.
pub struct OnceCell<T> {
    initialized: AtomicBool,
    lock: Spinlock<()>,
    value: UnsafeCell<MaybeUninit<T>>,
}

impl<T> OnceCell<T> {
    pub const fn new() -> Self {
        Self {
            initialized: AtomicBool::new(false),
            lock: Spinlock::new(()),
            value: UnsafeCell::new(MaybeUninit::uninit()),
        }
    }

    /// Unsafely deinitializes the cell, returning the contents.
    ///
    /// # Safety
    ///
    /// This operation is extremely dangerous. The caller needs to guarantee
    /// that there are no references to the contents of the cell or this will
    /// trigger undefined behaviour.
    pub unsafe fn deinit(&self) -> Option<T> {
        if !self.initialized.load(Ordering::Acquire) {
            return None;
        }

        let _lock = self.lock.lock();

        if !self.initialized.load(Ordering::Acquire) {
            return None;
        }

        let old = unsafe { core::mem::replace(&mut *self.value.get(), MaybeUninit::uninit()) };
        self.initialized.store(false, Ordering::Release);

        Some(unsafe { old.assume_init() })
    }

    /// Gets a reference to the inner value if the cell has been initialized.
    pub fn get(&self) -> Option<&T> {
        if !self.initialized.load(Ordering::Acquire) {
            return None;
        }
        // Safety: there are no mutable references to the inner value if `initialized`
        // is set to `true`, and the value has been initialized, so it is safe
        // to create a new shared reference and assume it is initialized.
        Some(unsafe { (*self.value.get()).assume_init_ref() })
    }

    /// Sets the inner value of the cell if it has not been initialized.
    ///
    /// If it has been initialized the inner value is not updated and the
    /// passed-in value is returned in the error.
    pub fn set(&self, value: T) -> Result<(), T> {
        // Do an initial check to see whether the value has been initialized.
        if !self.initialized.load(Ordering::Acquire) {
            // Lock to make sure we have exclusive access.
            let _lock = self.lock.lock();
            // Double check that someone else didn't initialize while we were waiting to get
            // the lock. Relaxed ordering is sufficient since the lock acts as a
            // memory barrier and also ensures no concurrent access to the code
            // that stores the value.
            if !self.initialized.load(Ordering::Relaxed) {
                // Safety: the combination of the lock and the fact that `initialized` is
                // `false` ensures that we have exclusive access to the inner
                // value, so taking a mutable reference to it is safe.
                unsafe { &mut *self.value.get() }.write(value);
                self.initialized.store(true, Ordering::Release);
                return Ok(());
            }
        }
        Err(value)
    }
}

impl<T> Default for OnceCell<T> {
    fn default() -> Self {
        Self::new()
    }
}

// Safety: It is safe to share references across threads since the inner value
// will only be set while an exclusive lock is held and only once. Until it is
// set there can be no shared references to it, and once it is set, and there
// are potential shared references to it, it will never be modified again.
unsafe impl<T> Sync for OnceCell<T> where T: Send + Sync {}

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
