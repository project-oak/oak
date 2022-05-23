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
#![feature(bench_black_box)]
#![feature(custom_test_frameworks)]
// As we're in a `no_std` environment, testing requires special handling. This
// approach was inspired by https://os.phil-opp.com/testing/.
#![test_runner(crate::test_runner)]
#![reexport_test_harness_main = "test_main"]

use core::panic::PanicInfo;
use rust_hypervisor_firmware_subset::pvh;

#[no_mangle]
#[cfg(test)]
pub extern "C" fn rust64_start(_rdi: &pvh::StartInfo) -> ! {
    // Ensure that `PVH_NOTE` is not optimized away, otherwise we won't be able to boot our
    // kernel when testing.
    core::hint::black_box(&pvh::PVH_NOTE);
    test_main();
    kernel::i8042::shutdown();
}

#[no_mangle]
#[cfg(not(test))]
pub extern "C" fn rust64_start(rdi: &pvh::StartInfo) -> ! {
    kernel::start_kernel(rdi);
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("Error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    kernel::panic(info);
}

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[cfg(test)]
fn test_runner(tests: &[&dyn Fn()]) {
    for test in tests {
        test();
    }
}
