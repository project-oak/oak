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

#![no_std]
#![no_main]
#![feature(lang_items)]
#![feature(alloc_error_handler)]
#![feature(custom_test_frameworks)]
// As we're in a `no_std` environment, testing requires special handling. This
// approach was inspired by https://os.phil-opp.com/testing/.
#![test_runner(crate::test_runner)]
#![reexport_test_harness_main = "test_main"]

mod asm;
mod bootparam;
mod logging;
mod memory;
mod serial;

#[macro_use]
extern crate log;

use core::panic::PanicInfo;

#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, rsi: &bootparam::boot_params) -> ! {
    logging::init_logging();
    memory::init_allocator(&rsi);

    if cfg!(test) {
        #[cfg(test)]
        test_main();
        unreachable!("tests should have exited qemu");
    } else {
        main(rsi);
    }
}

fn main(_info: &bootparam::boot_params) -> ! {
    info!("In main!");
    let serial = serial::Serial::new();
    runtime::framing::handle_frames(serial).unwrap();
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    error!("PANIC: {}", info);
    loop {}
}

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[cfg(test)]
fn test_runner(tests: &[&dyn Fn()]) {
    for test in tests {
        test();
    }
}

// Make libm implementations available to the linker.
// The Rust compiler-builtins only does this for UEFI targets, not bare-metal.
// See https://github.com/rust-lang/compiler-builtins/blob/master/src/math.rs#L23

#[no_mangle]
extern "C" fn fmod(a: f64, b: f64) -> f64 {
    libm::fmod(a, b)
}

#[no_mangle]
extern "C" fn fmodf(a: f32, b: f32) -> f32 {
    libm::fmodf(a, b)
}
