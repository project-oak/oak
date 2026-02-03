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

use core::panic::PanicInfo;

use elf::parse_elf_file;
use oak_linux_boot_params::BootParams;
use x86_64::{
    VirtAddr,
    instructions::{hlt, interrupts::int3},
};

/// Entry point for the 64-bit Rust code.
///
/// We ignore the first parameter in the Linux boot protocol, which must be 0.
#[unsafe(no_mangle)]
pub extern "C" fn rust64_start(_rdi: u64, boot_params: &BootParams) -> ! {
    let payload = include_bytes!(env!("PAYLOAD_PATH"));
    let entry = parse_elf_file(payload, boot_params.e820_table(), boot_params.ramdisk());
    // Safety: we successfully parsed the ELF file and found the entry point for it.
    unsafe { jump_to_kernel(entry, boot_params as *const _ as usize) }
}

/// Passes control to the extracted kernel.
///
/// The stack is reset without dropping anything that is currently allocated on
/// the stack. This is OK, since the wrapper code and data structures will
/// essentially disappear after the jump. No structures in the wrapper are
/// intended to outlive the wrapper itself.
///
/// # Safety
///
/// This assumes that the kernel entry point is valid.
unsafe fn jump_to_kernel(entry_point: VirtAddr, zero_page: usize) -> ! {
    unsafe {
        core::arch::asm!(
            // Reset the boot stack.
            "lea stack_start(%rip), %rsp",
            // Set the address of the boot parameters.
            "mov {1}, %rsi",
            // Jump to the kernel entrypoint.
            "jmp *{0}",
            in(reg) entry_point.as_u64(),
            in(reg) zero_page as u64,
            options(noreturn, att_syntax)
        );
    }
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    abort()
}

fn abort() -> ! {
    // Trigger a breakpoint exception. As we don't have a #BP handler, this will
    // triple fault and terminate the program.
    int3();

    loop {
        hlt();
    }
}
