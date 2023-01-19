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

use crate::syscall::mmap::mmap;
use core::arch::asm;
use goblin::elf64::program_header::{ProgramHeader, PF_W, PF_X, PT_LOAD};
use oak_restricted_kernel_interface::syscalls::{MmapFlags, MmapProtection};
use x86_64::{
    structures::paging::{PageSize, Size2MiB},
    VirtAddr,
};

/// Parses a pre-loaded ELF file, lays it out in memory, and passes control to it.
///
/// # Safety
///
/// We expect there to be an ELF file loaded in the memory pointed to by `payload`. If the pointer
/// does not point to a valid ELF file, the behaviour is undefined.
pub unsafe fn run_payload(payload: *const u8) -> ! {
    // Unfortunately we can't parse the whole file as an &[u8], as we don't know the size of the
    // embeded file. We only know where it starts. However, we know the ELF header is 64 bytes,
    // so assuming we have a valid file in there, we shouldn't cause UB here by accessing memory
    // outside our boundaries.
    let raw_header =
        core::slice::from_raw_parts(payload, goblin::elf::header::header64::SIZEOF_EHDR);
    let header = goblin::elf::Elf::parse_header(raw_header).unwrap();
    let phdrs = ProgramHeader::from_raw_parts(
        (payload as u64 + header.e_phoff) as *const ProgramHeader,
        header.e_phnum as usize,
    );

    for phdr in phdrs.iter().filter(|&phdr| phdr.p_type == PT_LOAD) {
        let vaddr = VirtAddr::new(phdr.p_vaddr).align_down(Size2MiB::SIZE);

        let mut prot = MmapProtection::PROT_READ;
        if phdr.p_flags & PF_W > 0 {
            prot |= MmapProtection::PROT_WRITE;
        }
        if phdr.p_flags & PF_X > 0 {
            prot |= MmapProtection::PROT_EXEC;
        }

        // As we need memory in the user space anyway, use the `mmap()` syscall that will allocate
        // physical frames and sets up user-accessible page tables for us.
        // Note that the expectation here is that all the sections are nicely 2 MiB-aligned,
        // otherwise the mmap() will fail.
        mmap(
            Some(vaddr),
            phdr.p_memsz as usize,
            prot,
            MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE | MmapFlags::MAP_FIXED,
        )
        .expect("failed to allocate user memory");

        core::ptr::copy_nonoverlapping(
            (payload as u64 + phdr.p_offset) as *const u8,
            phdr.p_vaddr as *mut u8,
            phdr.p_filesz as usize,
        );
    }
    // Set up the userspace stack at the end of the lower half of the virtual address space.
    // Well... almost. It's one page lower than the very end, as otherwise the initial stack pointer
    // would need to be a noncanonical address, so let's avoid that whole mess by moving down a bit.
    let rsp = VirtAddr::new(0x8000_0000_0000 - Size2MiB::SIZE);
    mmap(
        Some(rsp - Size2MiB::SIZE),
        Size2MiB::SIZE as usize,
        MmapProtection::PROT_READ | MmapProtection::PROT_WRITE,
        MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE | MmapFlags::MAP_FIXED,
    )
    .expect("failed to allocate memory for user stack");

    // Enter Ring 3 and jump to user code.
    asm! {
        "mov rsp, {}", // user stack
        "sysretq",
        in(reg) rsp.as_u64() - 8, // maintain stack alignment
        in("rcx") header.e_entry, // initial RIP
        in("r11") 0x202, // initial RFLAGS
        options(noreturn)
    }
}
