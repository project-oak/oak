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

use alloc::boxed::Box;
use core::{arch::asm, pin::Pin};

use anyhow::{Context, Result, anyhow};
use goblin::{
    elf::{Elf, ProgramHeader, ProgramHeaders},
    elf64::program_header::{PF_W, PF_X, PT_LOAD},
};
use oak_restricted_kernel_interface::syscalls::{MmapFlags, MmapProtection};
use self_cell::self_cell;
use x86_64::{
    VirtAddr,
    structures::paging::{PageSize, Size2MiB},
};

use crate::syscall::mmap::mmap;

// Set up the userspace stack at the end of the lower half of the virtual
// address space. Well... almost. It's one page lower than the very end, as
// otherwise the initial stack pointer would need to be a noncanonical address,
// so let's avoid that whole mess by moving down a bit.
static APPLICATION_STACK_VIRT_ADDR: u64 = 0x8000_0000_0000 - Size2MiB::SIZE;

self_cell!(
    /// Self-referential struct so that we don't have to parse the ELF file
    /// multiple times.
    struct Binary {
        owner: Box<[u8]>,

        #[covariant]
        dependent: Elf,
    }
);

/// Parsed Elf executeable representing a Restricted Application.
pub struct ElfExecuteable {
    binary: Binary,
}

impl ElfExecuteable {
    /// Attempts to parse the provided binary blob as an ELF file representing
    /// a Restricted Application.
    pub fn new(blob: Box<[u8]>) -> Result<Self> {
        Ok(ElfExecuteable {
            binary: Binary::try_new(blob, |boxed| {
                goblin::elf::Elf::parse(boxed)
                    .map_err(|err| anyhow!("failed to parse ELF file: {}", err))
            })?,
        })
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
        // In Oak Restricted Kernel, we prefer 2 MiB pages, so round down the segment
        // address if it isn't aligned on a 2 MiB page boundary.
        let vaddr = VirtAddr::new(phdr.p_vaddr).align_down(Size2MiB::SIZE);
        // As we've aligned the address down, we may need extra memory to account for
        // the padding.
        let size = ((phdr.p_vaddr - vaddr.as_u64()) + phdr.p_memsz) as usize;

        // PROT_READ is always implied; it's not possible to have a page that's, say,
        // executable but not readable.
        let mut prot = MmapProtection::PROT_READ;
        if phdr.p_flags & PF_W > 0 {
            prot |= MmapProtection::PROT_WRITE;
        }
        if phdr.p_flags & PF_X > 0 {
            prot |= MmapProtection::PROT_EXEC;
        }

        // As we need memory in the user space anyway, use the `mmap()` syscall that
        // will allocate physical frames and sets up user-accessible page tables
        // for us. Note that the expectation here is that all the sections are
        // nicely 2 MiB-aligned, otherwise the mmap() will fail.
        mmap(
            Some(vaddr),
            size,
            prot,
            MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE | MmapFlags::MAP_FIXED,
        )
        .expect("failed to allocate user memory");

        // Safety: we know the target memory is valid as we've just allocated it with
        // mmap().
        unsafe {
            core::ptr::copy_nonoverlapping(
                self.slice(phdr.p_offset, phdr.p_filesz).as_ptr(),
                phdr.p_vaddr as *mut u8,
                phdr.p_filesz as usize,
            );
        }

        Ok(())
    }

    /// Maps the application into virtual memory and returns the entrypoint.
    ///
    /// # Safety
    ///
    /// The application must be built from a valid ELF file representing an Oak
    /// Restricted Application.
    pub(self) unsafe fn map_into_memory(&self) -> VirtAddr {
        for phdr in self.program_headers().iter().filter(|&phdr| phdr.p_type == PT_LOAD) {
            self.load_segment(phdr).unwrap();
        }

        mmap(
            Some(VirtAddr::new(APPLICATION_STACK_VIRT_ADDR) - Size2MiB::SIZE),
            Size2MiB::SIZE as usize,
            MmapProtection::PROT_READ | MmapProtection::PROT_WRITE,
            MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE | MmapFlags::MAP_FIXED,
        )
        .expect("failed to allocate memory for user stack");

        self.entry()
    }
}

fn identify_pml4_frame(
    pml4: &x86_64::structures::paging::PageTable,
) -> Result<x86_64::structures::paging::PhysFrame, anyhow::Error> {
    let phys_addr = {
        let addr = pml4 as *const x86_64::structures::paging::PageTable;
        let pt_guard = crate::PAGE_TABLES.lock();
        let pt = pt_guard.get().context("failed to get page tables")?;
        crate::mm::Translator::translate_virtual(pt, VirtAddr::from_ptr(addr))
            .context("failed to translate virtual page table address")?
    };
    x86_64::structures::paging::PhysFrame::from_start_address(phys_addr)
        .map_err(anyhow::Error::msg)
        .context("couldn't get the physical frame for page table address")
}

pub struct Process {
    pml4: Pin<Box<x86_64::structures::paging::PageTable, alloc::alloc::Global>>,
    entry: VirtAddr,
}

impl Process {
    /// Creates a process from the application, without executing it.
    ///
    /// # Safety
    ///
    /// The process must be built from a valid ELF file representing an Oak
    /// Restricted Application.
    pub unsafe fn from_elf_executeable(
        elf_executeable: &ElfExecuteable,
    ) -> Result<Self, anyhow::Error> {
        let pml4 = crate::BASE_L4_PAGE_TABLE.get().context("base l4 table should be set")?.clone();
        // Load the process's page table, so the application can be loaded into its
        // memory. Hold onto the previous PT, so we can revert to it once the
        // application has been mapped into the process pt.
        let mut outer_prev_page_table = {
            let pml4_frame = identify_pml4_frame(&pml4).context("could not get pml4 frame")?;
            // Safety: the new page table maintains the same mappings for kernel space.
            unsafe { crate::PAGE_TABLES.lock().replace(pml4_frame) }
                .context("at this point there should be a previous root pt")?
                .into_inner()
        };

        // Safety: caller ensured the application is a valid ELF file representing an
        // Oak Restricted Application.
        let entry = unsafe { elf_executeable.map_into_memory() };

        // We've mapped the memory into the process page tables. Let's revert to the
        // previous page table.
        {
            let mapped_prev_pt = outer_prev_page_table.inner().lock();
            let prev_page_table = mapped_prev_pt.level_4_table();
            let pml4_frame =
                identify_pml4_frame(prev_page_table).context("could not get pml4 frame")?;
            // Safety: the new page table maintains the same mappings for kernel space.
            unsafe { crate::PAGE_TABLES.lock().replace(pml4_frame) };
        }
        Ok(Self { pml4, entry })
    }
    /// Executes the process.
    ///
    /// Safety: syscalls must have been registered. Changes the root page table,
    /// so addresses in userspace will be invalid. Caller must ensure those side
    /// effects are okay. Process must have been created with a valid elf file.
    pub unsafe fn execute(&self) -> anyhow::Result<!> {
        let pml4_frame = identify_pml4_frame(&self.pml4).expect("could not get pml4 frame");

        let pid = unsafe { crate::syscall::GsData::register_process(pml4_frame)? };
        unsafe {
            crate::syscall::GsData::set_current_pid(pid)?;
        }

        let entry = self.entry;
        unsafe {
            asm! {
                "mov rsp, {}", // user stack
                "sysretq",
                in(reg) APPLICATION_STACK_VIRT_ADDR - 8,
                in("rcx") entry.as_u64(), // initial RIP
                in("r11") 0x202, // initial RFLAGS (interrupts enabled)
                options(noreturn)
            }
        }
    }
}
