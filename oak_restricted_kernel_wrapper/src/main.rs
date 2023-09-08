//
// Copyright 2023 The Project Oak Authors
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

mod asm;
mod elf;

use core::{ffi::c_void, panic::PanicInfo};
use elf::parse_elf_file;
use oak_linux_boot_params::BootParams;
use x86_64::{
    instructions::{hlt, interrupts::int3},
    VirtAddr,
};

extern "C" {
    #[link_name = "stack_start"]
    static BOOT_STACK_POINTER: c_void;
}

/// Entry point for the 64-bit Rust code.
///
/// We ignore the first parameter in the Linux boot protocol, which must be 0.
#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, boot_params: &BootParams) -> ! {
    let payload = include_bytes!(env!("PAYLOAD_PATH"));
    let entry = parse_elf_file(payload, boot_params.e820_table());
    // Safety: we successfully parsed the ELF file and found the entry point for it.
    unsafe { jump_to_kernel(entry, boot_params as *const _ as usize) }
}

/// Passes control to the extracted kernel.
///
/// The stack is reset without dropping anything that was allocated on the stack.
///
/// # Safety
///
/// This assumes that the kernel entry point is valid.
unsafe fn jump_to_kernel(entry_point: VirtAddr, zero_page: usize) -> ! {
    core::arch::asm!(
        // Boot stack pointer
        "mov {1}, %rsp",
        // Zero page address
        "mov {2}, %rsi",
        // ...and away we go!
        "jmp *{0}",
        in(reg) entry_point.as_u64(),
        in(reg) &BOOT_STACK_POINTER as *const _ as u64,
        in(reg) zero_page as u64,
        options(noreturn, att_syntax)
    );
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    // Trigger a breakpoint exception. As we don't have a #BP handler, this will triple fault and
    // terminate the program.
    int3();

    loop {
        hlt();
    }
}
