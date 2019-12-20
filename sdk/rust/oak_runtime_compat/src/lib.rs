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

pub mod asylo;
pub mod common;

#[global_allocator]
static A: asylo::allocator::System = asylo::allocator::System;

/// Provide the entrypoint needed by the compiler's failure mechanisms when
/// `std` is unavailable.  See ["No
/// stdlib" documentation](https://doc.rust-lang.org/1.2.0/book/no-stdlib.html).
#[lang = "eh_personality"]
pub extern "C" fn eh_personality() {}

pub fn thread_test(x: i32) -> common::io::Result<i32> {
  use alloc::sync::Arc;
  use core::sync::atomic::{AtomicI32, Ordering};
  let val = Arc::new(AtomicI32::new(x));

  let other = {
    let val = Arc::clone(&val);
    move || {
      val.fetch_add(42, Ordering::SeqCst);
    }
  };

  let t = unsafe {
      // TODO: make safe thread interface in common/thread.rs
      asylo::thread::Thread::new(Box::new(other))
  }?;
  t.join();
  Ok(val.load(Ordering::SeqCst))
}

/// An exported placeholder function to check that linking against C++ is successful.
#[no_mangle]
pub extern "C" fn add_magic_number(x: i32) -> i32 {
    thread_test(x).unwrap_or(0)
}
