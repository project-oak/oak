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

// TODO(#662): Should this crate be merged into oak_platform or third_party/rust?

#![no_std]
#![feature(lang_items)]
#![feature(allocator_api)]
#![feature(alloc_prelude)]
#![feature(alloc_error_handler)]
#![feature(fn_traits)]
#![feature(rustc_private)]
#![feature(never_type)]
#![feature(box_syntax)]
#![feature(int_error_internals)]
#![feature(array_error_internals)]
#![feature(char_error_internals)]

extern crate alloc;

pub use alloc::prelude::v1::*;

pub use rust_asylo::error;
pub use rust_asylo::io;

mod allocator;
mod asylo;

#[global_allocator]
static A: allocator::System = allocator::System;

pub use rust_asylo::asylo::thread::JoinHandle;
pub use rust_asylo::asylo::thread::Thread;
pub use rust_asylo::asylo::thread::ThreadId;
pub use rust_asylo::asylo::Mutex;
pub use rust_asylo::asylo::RwLock;

/// A safe function to spawn an enclave thread. At the moment, parameters cannot
/// be passed in this function call, unlike the Rust standard library. (This can
/// be achieved by moving values into closures and spawning threads with said
/// closures)
pub fn spawn<F>(f: F) -> Thread
where
    F: FnOnce() -> (),
    F: Send + 'static,
{
    unsafe { Thread::new(Box::new(f)) }.expect("could not spawn thread!?")
}

/// Provide the entrypoint needed by the compiler's failure mechanisms when
/// `std` is unavailable.  See ["No
/// stdlib" documentation](https://doc.rust-lang.org/1.2.0/book/no-stdlib.html).
#[lang = "eh_personality"]
pub extern "C" fn eh_personality() {}
