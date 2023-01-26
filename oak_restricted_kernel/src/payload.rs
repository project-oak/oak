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
use alloc::{vec, vec::Vec};
use anyhow::Result;
use core::arch::asm;
use goblin::elf64::program_header::{PF_W, PF_X, PT_LOAD};
use oak_channel::Channel;
use oak_restricted_kernel_interface::syscalls::{MmapFlags, MmapProtection};
use x86_64::{
    structures::paging::{PageSize, Size2MiB, Size4KiB},
    VirtAddr,
};

/// Reads a chunk of data and acknowledges the transmission by writing back the number of bytes
/// read.
fn read_chunk<C: Channel + ?Sized>(channel: &mut C, chunk: &mut [u8]) -> Result<()> {
    let len: u32 = chunk
        .len()
        .try_into()
        .map_err(|_| anyhow::anyhow!("chunk too big"))?;
    channel.read(chunk)?;
    channel.write(&len.to_le_bytes())
}

/// Reads a payload blob, one page at a time, from the given channel.
pub fn read_payload<C: Channel + ?Sized>(channel: &mut C) -> Result<Vec<u8>> {
    let payload_len = {
        let mut buf: [u8; 4] = Default::default();
        channel.read(&mut buf)?;
        u32::from_le_bytes(buf)
    };
    let mut payload = vec![0; payload_len as usize];
    let mut chunks_mut = payload.array_chunks_mut::<{ Size4KiB::SIZE as usize }>();

    for chunk in chunks_mut.by_ref() {
        read_chunk(channel, chunk)?;
    }
    read_chunk(channel, chunks_mut.into_remainder())?;

    Ok(payload)
}

/// Parses a pre-loaded ELF file, lays it out in memory, and passes control to it.
pub fn run_payload(payload: &[u8]) -> ! {
    let elf = goblin::elf::Elf::parse(payload).expect("failed to parse application binary");

    for phdr in elf
        .program_headers
        .iter()
        .filter(|&phdr| phdr.p_type == PT_LOAD)
    {
        let vaddr = VirtAddr::new(phdr.p_vaddr).align_down(Size2MiB::SIZE);
        let padding = phdr.p_vaddr - vaddr.as_u64();

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
        log::info!(
            "allocating memory for section: addr = {:#018x}, size = {:x} + {:x}",
            vaddr.as_u64(),
            padding,
            phdr.p_memsz
        );
        mmap(
            Some(vaddr),
            (padding + phdr.p_memsz) as usize,
            prot,
            MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE | MmapFlags::MAP_FIXED,
        )
        .expect("failed to allocate user memory");

        // Safety: we know the target memory is valid as we've just allocated it with mmap().
        unsafe {
            core::ptr::copy_nonoverlapping(
                (payload.as_ptr() as u64 + phdr.p_offset) as *const u8,
                phdr.p_vaddr as *mut u8,
                phdr.p_filesz as usize,
            );
        }
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
    // Safety: by now, if we're here, we've loaded a valid ELF file. It's up to the user to
    // guarantee that the file made sense.
    unsafe {
        asm! {
            "mov rsp, {}", // user stack
            "sysretq",
            in(reg) rsp.as_u64() - 8, // maintain stack alignment
            in("rcx") elf.entry, // initial RIP
            in("r11") 0x002, // initial RFLAGS (leave interrupts disabled)
            options(noreturn)
        }
    }
}
