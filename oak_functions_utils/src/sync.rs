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
    hint::spin_loop,
    sync::atomic::{AtomicBool, Ordering},
};
use lock_api::{GuardSend, RawMutex};

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
