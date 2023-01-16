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
#![feature(alloc_error_handler)]
#![feature(naked_functions)]

use core::{arch::asm, panic::PanicInfo};
use oak_linux_boot_params::BootParams;

// Placeholder payload that triggers an undefined instruction fault.
// We do this here for three reasons:
// a) It provides a convenient way to figure out the address of the payload.
// b) It stops the compiler and linker from optimizing away the whole section.
// c) It's invalid as both code and as an ELF file, so should trigger an error no matter whether we
//    try to execute it ourselves or try to parse it as an ELF file.
// (A more clever thing would be to embed an ELF file here that causes an ud2...)
#[naked]
#[link_section = ".payload"]
extern "C" fn payload() -> ! {
    unsafe {
        asm!("ud2", options(noreturn));
    }
}

#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, rsi: &BootParams) -> ! {
    oak_restricted_kernel::start_kernel(rsi);
    // Safety: the expectation is that the payload will contain a valid ELF file.
    unsafe {
        oak_restricted_kernel::run_payload(&payload as *const _ as *const u8);
    }
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_restricted_kernel::panic(info);
}
