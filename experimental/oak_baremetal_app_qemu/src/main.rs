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
#![feature(core_c_str)]
#![feature(core_ffi_c)]
#![feature(custom_test_frameworks)]
// As we're in a `no_std` environment, testing requires special handling. This
// approach was inspired by https://os.phil-opp.com/testing/.
#![test_runner(crate::test_runner)]
#![reexport_test_harness_main = "test_main"]

use core::panic::PanicInfo;

mod hvm_start_info;
#[cfg(all(feature = "multiboot", not(test)))]
mod multiboot;

#[no_mangle]
#[cfg(test)]
pub extern "C" fn rust64_start(_rdi: &hvm_start_info::hvm_start_info) -> ! {
    test_main();
    oak_baremetal_kernel::i8042::shutdown();
}

#[no_mangle]
#[cfg(all(not(test), feature = "multiboot"))]
pub extern "C" fn rust64_start(start_info: &multiboot::multiboot_info, magic: u64) -> ! {
    // The magic constant is specified in multiboot.h.
    // See <https://www.gnu.org/software/grub/manual/multiboot/multiboot.html#Machine-state>
    // for a full specification of the initial machine state.
    // As at this stage we don't even have logging set up, so if the magic does not match,
    // let's just shut down the machine.
    if magic != 0x2BADB002 {
        oak_baremetal_kernel::i8042::shutdown();
    }
    oak_baremetal_kernel::start_kernel(start_info);
}

#[no_mangle]
#[cfg(all(not(test), not(feature = "multiboot")))]
pub extern "C" fn rust64_start(start_info: &hvm_start_info::hvm_start_info) -> ! {
    oak_baremetal_kernel::start_kernel(start_info);
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("Error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_baremetal_kernel::panic(info);
}

#[lang = "eh_personality"]
extern "C" fn eh_personality() {}

#[cfg(test)]
fn test_runner(tests: &[&dyn Fn()]) {
    for test in tests {
        test();
    }
}
