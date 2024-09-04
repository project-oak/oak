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
    structures::paging::{PageSize, Size4KiB},
    VirtAddr,
};

extern "C" {
    // The start of the bootable code. We use this to determine the offset at which
    // the wrapper binary was loaded into memory.
    #[link_name = "boot_start"]
    static BOOT_START: c_void;
    // The start of the relocation information for the wrapper.
    #[link_name = "rela_start"]
    static RELA_START: c_void;
    // The end of the relocation information for the wrapper.
    #[link_name = "rela_end"]
    static RELA_END: c_void;
    // The start of the data section of the binary. We use this to make sure all
    // relocations are done in writable data pages in memory.
    #[link_name = "data_start"]
    static DATA_START: c_void;
    // The end of the data section of the binary. We use this to make sure all
    // relocations are done in writable data pages in memory.
    #[link_name = "data_end"]
    static DATA_END: c_void;
}

/// Entry point for the 64-bit Rust code.
///
/// We ignore the first parameter in the Linux boot protocol, which must be 0.
#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, boot_params: &BootParams) -> ! {
    // Safety: we run this to patch all relocations before any other Rust code is
    // executed.
    unsafe {
        patch_self_relocations();
    }
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

/// Finds and patches the relocations within this binary.
///
/// #Safety
///
/// This function must be called before any rust code is executed that rely on
/// the relocations that this is patching, otherwise dereferencing the unpatched
/// relocations will lead to undefined behavior.
///
/// If this code panics it will cause undefined behavior since the panic unwind
/// logic relies on the relocations, so instead of panicking abort will be
/// called directly on any errors.
unsafe fn patch_self_relocations() {
    // Safety: we're not going to dereference any of the memory locations, we're
    // just interested in the pointer addresses.
    let (boot_start, rela_start, rela_end, data_start, data_end) = unsafe {
        (
            VirtAddr::from_ptr(&BOOT_START as *const _),
            VirtAddr::from_ptr(&RELA_START as *const _),
            VirtAddr::from_ptr(&RELA_END as *const _),
            VirtAddr::from_ptr(&DATA_START as *const _),
            VirtAddr::from_ptr(&DATA_END as *const _),
        )
    };
    // The first 4KiB is used by the setup data in the extracted binary, so the
    // effective offset for calculating relocations is 4KiB before BOOT_START.
    let base_offset = boot_start - Size4KiB::SIZE;
    if rela_end < rela_start {
        abort();
    }
    let rela_size = (rela_end - rela_start) as usize;
    // Safety: we rely on the correctness of the linker script to ensure that these
    // addresses point to the valid relocation slice in memory.
    let rela: &[u8] = unsafe { core::slice::from_raw_parts(rela_start.as_ptr(), rela_size) };
    if elf::patch_relocations(rela, base_offset, data_start, data_end).is_err() {
        // We can't continue if the relocations were not successful.
        abort();
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
