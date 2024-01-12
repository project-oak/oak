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

use alloc::{boxed::Box, format, vec};
use core::arch::asm;

use anyhow::{anyhow, Result};
use goblin::{
    elf::{Elf, ProgramHeader, ProgramHeaders},
    elf64::program_header::{PF_W, PF_X, PT_LOAD},
};
use oak_channel::Channel;
use oak_restricted_kernel_interface::syscalls::{MmapFlags, MmapProtection};
use self_cell::self_cell;
use sha2::{Digest, Sha256};
use x86_64::{
    structures::paging::{PageSize, Size2MiB, Size4KiB},
    VirtAddr,
};

use crate::syscall::mmap::mmap;

/// Reads a chunk of data and acknowledges the transmission by writing back the number of bytes
/// read.
fn read_chunk<C: Channel + ?Sized>(channel: &mut C, chunk: &mut [u8]) -> Result<()> {
    let len: u32 = chunk
        .len()
        .try_into()
        .map_err(|_| anyhow::anyhow!("chunk too big"))?;
    channel.read_exact(chunk)?;
    channel.write_all(&len.to_le_bytes())
}

self_cell!(
    /// Self-referential struct so that we don't have to parse the ELF file multiple times.
    struct Binary {
        owner: Box<[u8]>,

        #[covariant]
        dependent: Elf,
    }
);

/// Representation of an Restricted Application that the Restricted Kernel can run.
pub struct Application {
    binary: Binary,
    digest: [u8; 32],
}

impl Application {
    /// Loads a Restricted Application over the given channel using a basic framed format.
    ///
    /// This is intended for use after the kernel has started up to load the Restricted Application,
    /// before we start the application and hand off the channel to it.
    ///
    /// The protocol to load the application is very simple:
    /// 1. loader sends the size of the application binary, as u32
    /// 2. loader sends max 4 KiB of data and waits for the kernel to acknowledge
    /// 3. kernel reads up to 4 KiB of data and acks by responding with the amount of data read
    /// 4. repeat (2) and (3) until all the data has been transmitted
    pub fn load_raw<C: Channel + ?Sized>(channel: &mut C) -> Result<Self> {
        let payload_len = {
            let mut buf: [u8; 4] = Default::default();
            channel.read_exact(&mut buf)?;
            u32::from_le_bytes(buf)
        };
        let mut payload = vec![0; payload_len as usize];
        let mut chunks_mut = payload.array_chunks_mut::<{ Size4KiB::SIZE as usize }>();

        for chunk in chunks_mut.by_ref() {
            read_chunk(channel, chunk)?;
        }
        read_chunk(channel, chunks_mut.into_remainder())?;
        log::info!("Binary loaded, size: {}", payload.len());

        Self::new(payload.into_boxed_slice())
    }

    /// Attempts to parse the provided binary blob as an ELF file representing an Restricted
    /// Application.
    pub fn new(blob: Box<[u8]>) -> Result<Self> {
        let digest = Sha256::digest(&blob[..]).into();

        Ok(Application {
            binary: Binary::try_new(blob, |boxed| {
                goblin::elf::Elf::parse(boxed)
                    .map_err(|err| anyhow!("failed to parse ELF file: {}", err))
            })?,
            digest,
        })
    }

    pub fn digest(&self) -> &[u8] {
        &self.digest[..]
    }

    fn program_headers(&self) -> &ProgramHeaders {
        &self.binary.borrow_dependent().program_headers
    }

    fn entry(&self) -> VirtAddr {
        VirtAddr::new(self.binary.borrow_dependent().entry)
    }

    fn slice(&self, start: u64, limit: u64) -> &[u8] {
        &self.binary.borrow_owner()[start as usize..(start + limit) as usize]
    }

    fn load_segment(&self, phdr: &ProgramHeader) -> Result<()> {
        // In Oak Restricted Kernel, we prefer 2 MiB pages, so round down the segment address if it
        // isn't aligned on a 2 MiB page boundary.
        let vaddr = VirtAddr::new(phdr.p_vaddr).align_down(Size2MiB::SIZE);
        // As we've aligned the address down, we may need extra memory to account for the
        // padding.
        let size = ((phdr.p_vaddr - vaddr.as_u64()) + phdr.p_memsz) as usize;

        // PROT_READ is always implied; it's not possible to have a page that's, say, executable but
        // not readable.
        let mut prot = MmapProtection::PROT_READ;
        if phdr.p_flags & PF_W > 0 {
            prot |= MmapProtection::PROT_WRITE;
        }
        if phdr.p_flags & PF_X > 0 {
            prot |= MmapProtection::PROT_EXEC;
        }

        // As we need memory in the user space anyway, use the `mmap()` syscall that will
        // allocate physical frames and sets up user-accessible page tables for us.
        // Note that the expectation here is that all the sections are nicely 2 MiB-aligned,
        // otherwise the mmap() will fail.
        mmap(
            Some(vaddr),
            size,
            prot,
            MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE | MmapFlags::MAP_FIXED,
        )
        .expect("failed to allocate user memory");

        // Safety: we know the target memory is valid as we've just allocated it with mmap().
        unsafe {
            core::ptr::copy_nonoverlapping(
                self.slice(phdr.p_offset, phdr.p_filesz).as_ptr(),
                phdr.p_vaddr as *mut u8,
                phdr.p_filesz as usize,
            );
        }

        Ok(())
    }

    /// Maps the application into virtual memory and passes control to it.
    ///
    /// # Safety
    ///
    /// The application must be built from a valid ELF file representing an Oak Restricted
    /// Application, and there must not be an active application as we alter the virtual memory
    /// mappings.
    pub unsafe fn run(&self) -> ! {
        for phdr in self
            .program_headers()
            .iter()
            .filter(|&phdr| phdr.p_type == PT_LOAD)
        {
            self.load_segment(phdr).unwrap();
        }

        // Set up the userspace stack at the end of the lower half of the virtual address space.
        // Well... almost. It's one page lower than the very end, as otherwise the initial stack
        // pointer would need to be a noncanonical address, so let's avoid that whole mess
        // by moving down a bit.
        let rsp = VirtAddr::new(0x8000_0000_0000 - Size2MiB::SIZE);
        mmap(
            Some(rsp - Size2MiB::SIZE),
            Size2MiB::SIZE as usize,
            MmapProtection::PROT_READ | MmapProtection::PROT_WRITE,
            MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE | MmapFlags::MAP_FIXED,
        )
        .expect("failed to allocate memory for user stack");

        log::info!(
            "Running application; binary hash: {}",
            self.digest.map(|x| format!("{:02x}", x)).join("")
        );

        // Enter Ring 3 and jump to user code.
        // Safety: by now, if we're here, we've loaded a valid ELF file. It's up to the user to
        // guarantee that the file made sense.
        unsafe {
            asm! {
                "mov rsp, {}", // user stack
                "sysretq",
                in(reg) rsp.as_u64() - 8,
                in("rcx") self.entry().as_u64(), // initial RIP
                in("r11") 0x202, // initial RFLAGS (interrupts enabled)
                options(noreturn)
            }
        }
    }
}
