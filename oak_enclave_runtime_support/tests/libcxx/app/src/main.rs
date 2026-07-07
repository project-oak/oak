//
// Copyright 2026 The Project Oak Authors
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

//! C++ FFI test application for Oak Restricted Kernel.
//!
//! Demonstrates calling C++ standard library functions from Rust inside an
//! enclave application linked against LLVM libc and libc++. Exercises
//! `std::sort`, `std::vector`, `std::string`, and `std::unique_ptr`.

#![no_std]
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use oak_restricted_kernel_sdk::entrypoint;

// Helper C++ functions implemented in `cc/cxx_demo.cc`. They internally use
// LLVM libc++ (containers, algorithms, smart pointers) on top of the Oak LLVM
// libc port. The libc's OS-level vendor callbacks (heap, exit, stdio) are
// provided by `oak_enclave_runtime_support`, which every enclave application
// links via the SDK, so nothing libc-specific needs to live here.
unsafe extern "C" {
    fn cxx_sort_array(data: *mut i32, len: usize);
    fn cxx_vector_sum(count: usize) -> i64;
    fn cxx_format_greeting(name: *const u8) -> *mut u8;
    fn cxx_free_string(s: *mut u8);
    fn cxx_unique_ptr_test(value: i32) -> i32;
    fn cxx_stdio_test();
}

#[entrypoint]
fn run_cxx_demo() -> ! {
    log::set_max_level(log::LevelFilter::Info);

    // Test 1: std::sort
    let mut data = [5i32, 3, 8, 1, 9, 2, 7, 4, 6, 0];
    unsafe { cxx_sort_array(data.as_mut_ptr(), data.len()) };
    for (i, field) in data.iter().enumerate() {
        assert_eq!(*field, i as i32, "sort mismatch at index {i}");
    }
    log::info!("std::sort test passed");

    // Test 2: std::vector with heap allocation
    let sum = unsafe { cxx_vector_sum(100) };
    // Sum of 0..99 = 99 * 100 / 2 = 4950
    assert_eq!(sum, 4950, "vector sum mismatch");
    log::info!("std::vector sum test passed (sum = {sum})");

    // Test 3: std::string formatting
    let name = b"Oak Restricted Kernel\0";
    let greeting = unsafe { cxx_format_greeting(name.as_ptr()) };
    assert!(!greeting.is_null(), "string allocation failed");
    let msg = unsafe { core::ffi::CStr::from_ptr(greeting as *const core::ffi::c_char) };
    let msg_str = msg.to_str().unwrap_or("invalid UTF-8");
    assert_eq!(msg_str, "Hello, Oak Restricted Kernel!");
    log::info!("std::string test passed: {msg_str}");
    unsafe { cxx_free_string(greeting) };

    // Test 4: std::unique_ptr
    let result = unsafe { cxx_unique_ptr_test(21) };
    assert_eq!(result, 42, "unique_ptr test mismatch");
    log::info!("std::unique_ptr test passed (result = {result})");

    // Test 5: C FILE* stdio (fprintf/fwrite to stderr) routed through the Oak
    // libc vendor callbacks to the serial console.
    unsafe { cxx_stdio_test() };

    log::info!("all C++ tests passed");
    oak_restricted_kernel_interface::syscall::exit(0);
}
