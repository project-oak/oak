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

use crate::common::io;
use crate::alloc::boxed::Box;

// TODO: Enclave backend that provides:
// - Allocator
// - Threads
// - Mutexes
// - TODO: Channel with automatic remote attestation
mod asylo;
pub use self::asylo::*;

/// A safe function to spawn an enclave thread. At the moment, parameters cannot
/// be passed in this function call, unlike the rust standard library. (This can
/// be achieved by moving values into closures and spawning threads with said
/// closures)
pub fn spawn<F>(f: F) -> io::Result<thread::Thread>
where
    F: FnOnce() -> (),
    F: Send + 'static,
{
    unsafe {
      thread::Thread::new(Box::new(f))
    }
}
