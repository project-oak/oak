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

//! Functionality to allow use of Rust code within the Oak Runtime.

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
extern crate core;
extern crate libc;

use alloc::prelude::v1::*;
use core::alloc::Layout;
use core::panic::PanicInfo;

// TODO: Move to separate crate.
pub mod error;
pub mod io;
pub mod asylo_alloc;
pub mod thread;
pub mod mutex;

// TODO: Move to separate crate and expose safe wrappers.
#[link(name = "sgx_trts")]
extern "C" {
    // SGX-enabled abort function that causes an undefined instruction (`UD2`) to be executed, which
    // terminates the enclave execution.
    //
    // The C type of this function is `extern "C" void abort(void) __attribute__(__noreturn__);`
    //
    // See https://github.com/intel/linux-sgx/blob/d166ff0c808e2f78d37eebf1ab614d944437eea3/sdk/trts/linux/trts_pic.S#L565.
    fn abort() -> !;
}

#[global_allocator]
static A: asylo_alloc::System = asylo_alloc::System;

// Define what happens in an Out Of Memory (OOM) condition.
#[alloc_error_handler]
fn alloc_error(_layout: Layout) -> ! {
    unsafe { abort() }
}

// See https://doc.rust-lang.org/nomicon/panic-handler.html.
#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    unsafe { abort() }
}

/// Provide the entrypoint needed by the compiler's failure mechanisms when
/// `std` is unavailable.  See ["No
/// stdlib" documentation](https://doc.rust-lang.org/1.2.0/book/no-stdlib.html).
#[lang = "eh_personality"]
pub extern "C" fn eh_personality() {}

/// An exported placeholder function to check that linking against C++ is successful.
/// It just adds "42" to the provided value and returns it to the caller.
#[no_mangle]
pub extern "C" fn add_magic_number(x: i32) -> i32 {
    // Allocate a bunch of elements on the heap in order to exercise the allocator.
    let v: Vec<i32> = (0..10).map(|n| n + 40).collect();
    x + v[2]
}
