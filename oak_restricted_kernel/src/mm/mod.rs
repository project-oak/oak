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

use goblin::{elf32::program_header::PT_LOAD, elf64::program_header::ProgramHeader};
use log::info;
use oak_linux_boot_params::{BootE820Entry, E820EntryType, Ramdisk};
use oak_sev_guest::msr::{SevStatus, get_sev_status};
use x86_64::{
    PhysAddr, VirtAddr,
    addr::{align_down, align_up},
    structures::paging::{
        FrameAllocator, Page, PageSize, PageTable, PageTableFlags as BasePageTableFlags, PhysFrame,
        Size2MiB, Size4KiB,
        frame::PhysFrameRange,
        mapper::{FlagUpdateError, MapToError, MapperFlush, UnmapError},
    },
};

use self::encrypted_mapper::{EncryptedPageTable, MemoryEncryption};
use crate::{FRAME_ALLOCATOR, PAGE_TABLES, VMA_ALLOCATOR};

mod bitmap_frame_allocator;
pub mod encrypted_mapper;
pub mod frame_allocator;
pub mod page_tables;
pub mod virtual_address_allocator;

/// The start of kernel memory.
pub const KERNEL_OFFSET: u64 = 0xFFFF_FFFF_8000_0000;

/// The offset used for the direct mapping of all physical memory.
const DIRECT_MAPPING_OFFSET: VirtAddr = VirtAddr::new_truncate(0xFFFF_8800_0000_0000);

/// For now we use a fixed position for the encrypted bit. For now we assume
/// that we will be running on AMD Arcadia-Milan CPUs, which use bit 51.
pub const ENCRYPTED_BIT_POSITION: u8 = 51;

// TODO(#3394): Move to a shared crate.
pub trait Translator {
    /// Translates the given virtual address to the physical address that it
    /// maps to.
    ///
    /// Returns `None` if there is no valid mapping for the given address.
    fn translate_virtual(&self, addr: VirtAddr) -> Option<PhysAddr>;

    /// Translate a physical address to a virtual address.
    ///
    /// Note that a physical address may be mapped multiple times. This function
    /// will always return the address from the directly mapped region,
    /// ignoring ohter mappings if they exist.
    fn translate_physical(&self, addr: PhysAddr) -> Option<VirtAddr>;

    /// Translate a physical frame to virtual page, using the directly mapped
    /// region.
    fn translate_physical_frame<S: PageSize>(&self, frame: PhysFrame<S>) -> Option<Page<S>>;
}

bitflags::bitflags! {
    /// Possible flags for a page table entry.
    ///
    /// See <x86_64::structures::paging::PageTableFlags> for more details.
    #[derive(Clone, Copy, Debug)]
    pub struct PageTableFlags: u64 {
        const PRESENT = 1;
        const WRITABLE = 1 << 1;
        const USER_ACCESSIBLE = 1 << 2;
        const WRITE_THROUGH = 1 << 3;
        const NO_CACHE = 1 << 4;
        const ACCESSED = 1<< 5;
        const DIRTY = 1 << 6;
        const HUGE_PAGE = 1 << 7;
        const GLOBAL = 1 << 8;
        /// Marks the page as encrypted. Ignored under <NoEncryption>.
        ///
        /// The bit value is hardcoded to be 51 here, but that's because it's not possible to
        /// represent `ENCRYPTED = 1 << C` in Rust right now. The actual bit set may not be 51.
        const ENCRYPTED = 1 << 51;
        const NO_EXECUTE = 1 << 63;
    }
}

impl From<PageTableFlags> for BasePageTableFlags {
    fn from(value: PageTableFlags) -> Self {
        let mut flags = BasePageTableFlags::empty();
        if value.contains(PageTableFlags::PRESENT) {
            flags |= BasePageTableFlags::PRESENT
        }
        if value.contains(PageTableFlags::WRITABLE) {
            flags |= BasePageTableFlags::WRITABLE
        }
        if value.contains(PageTableFlags::USER_ACCESSIBLE) {
            flags |= BasePageTableFlags::USER_ACCESSIBLE
        }
        if value.contains(PageTableFlags::WRITE_THROUGH) {
            flags |= BasePageTableFlags::WRITE_THROUGH
        }
        if value.contains(PageTableFlags::NO_CACHE) {
            flags |= BasePageTableFlags::NO_CACHE
        }
        if value.contains(PageTableFlags::ACCESSED) {
            flags |= BasePageTableFlags::ACCESSED
        }
        if value.contains(PageTableFlags::DIRTY) {
            flags |= BasePageTableFlags::DIRTY
        }
        if value.contains(PageTableFlags::HUGE_PAGE) {
            flags |= BasePageTableFlags::HUGE_PAGE
        }
        if value.contains(PageTableFlags::GLOBAL) {
            flags |= BasePageTableFlags::GLOBAL
        }
        // There is no equivalent of ENCRYPTED in BasePageTableFlags.
        if value.contains(PageTableFlags::NO_EXECUTE) {
            flags |= BasePageTableFlags::NO_EXECUTE
        }
        flags
    }
}

/// Page mapper for pages of type `<S>`.
///
/// This is equivalent to <x86_64::structures::paging::mapper::Mapper>, but
/// knows about memory encryption.
pub trait Mapper<S: PageSize> {
    unsafe fn map_to_with_table_flags(
        &self,
        page: Page<S>,
        frame: PhysFrame<S>,
        flags: PageTableFlags,
        parent_table_flags: PageTableFlags,
    ) -> Result<MapperFlush<S>, MapToError<S>>;

    /// Unmaps a page.
    ///
    /// # Safety
    ///
    /// No checks are done whether the page is actually in use or not.
    unsafe fn unmap(&self, page: Page<S>) -> Result<(PhysFrame<S>, MapperFlush<S>), UnmapError>;

    /// Changes the flags on a page table entry by unmapping and remapping it.
    ///
    /// # Safety
    ///
    /// There are many ways how changing page table entries can break memory
    /// safety or cause other failures, e.g. by setting the `NO_EXECUTE` bit
    /// on pages that contain your code or removing `WRITABLE` from the page
    /// that contains your stack.
    unsafe fn update_flags(
        &self,
        page: Page<S>,
        flags: PageTableFlags,
    ) -> Result<MapperFlush<S>, FlagUpdateError>;
}

pub fn init(memory_map: &[BootE820Entry], program_headers: &[ProgramHeader], ramdisk: &Ramdisk) {
    let mut alloc = FRAME_ALLOCATOR.lock();

    /* Step 1: mark all RAM as available (event though it may contain data!) */
    memory_map
        .iter()
        .inspect(|e| {
            info!(
                "E820 entry: [{:#018x}..{:#018x}) ({}), type {}",
                e.addr(),
                e.addr() + e.size(),
                e.size(),
                e.entry_type().unwrap()
            );
        })
        .filter(|e| e.entry_type() == Some(E820EntryType::RAM))
        .map(|e| {
            // Clip both ends, if necessary, to make sure that we are aligned with 2 MiB
            // pages.
            (
                PhysAddr::new(align_up(e.addr() as u64, Size2MiB::SIZE)),
                PhysAddr::new(align_down((e.addr() + e.size()) as u64, Size2MiB::SIZE)),
            )
        })
        .filter(|(start, limit)| limit > start)
        .map(|(start, limit)| {
            // Safety: align_down/align_up guarantees we're aligned to 2 MiB boundaries,
            // and we know there's _something_ in the memory range.
            PhysFrame::range(
                PhysFrame::from_start_address(start).unwrap(),
                PhysFrame::from_start_address(limit).unwrap(),
            )
        })
        .for_each(|range| alloc.mark_valid(range, true));

    // Step 2: mark known in-use regions as not available.

    // First, leave out the first 2 MiB as there be dragons (and bootloader data
    // structures)
    alloc.mark_valid(
        PhysFrame::range(
            PhysFrame::from_start_address(PhysAddr::new(0x0)).unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(Size2MiB::SIZE)).unwrap(),
        ),
        false,
    );

    // Second, mark every `PT_LOAD` section from the phdrs as used.
    program_headers
        .iter()
        .filter(|phdr| phdr.p_type == PT_LOAD)
        .map(|phdr| {
            // Align the physical addresses to 2 MiB boundaries, making them larger if
            // necessary.
            PhysFrame::range(
                PhysFrame::from_start_address(PhysAddr::new(align_down(
                    phdr.p_paddr,
                    Size2MiB::SIZE,
                )))
                .unwrap(),
                PhysFrame::from_start_address(PhysAddr::new(align_up(
                    phdr.p_paddr + phdr.p_memsz,
                    Size2MiB::SIZE,
                )))
                .unwrap(),
            )
        })
        .for_each(|range| {
            info!(
                "marking [{:#018x}..{:#018x}) as reserved",
                range.start.start_address().as_u64(),
                range.end.start_address().as_u64()
            );
            alloc.mark_valid(range, false)
        });

    let ramdisk_range = ramdisk_range(ramdisk);
    info!(
        "marking [{:#018x}..{:#018x}) as reserved (ramdisk)",
        ramdisk_range.start.start_address().as_u64(),
        ramdisk_range.end.start_address().as_u64()
    );
    alloc.mark_valid(ramdisk_range, false);
}

pub fn ramdisk_range(ramdisk: &Ramdisk) -> PhysFrameRange<Size2MiB> {
    PhysFrame::range(
        PhysFrame::<x86_64::structures::paging::Size2MiB>::from_start_address(PhysAddr::new(
            align_down(ramdisk.addr.into(), Size2MiB::SIZE),
        ))
        .unwrap(),
        PhysFrame::from_start_address(PhysAddr::new(align_up(
            (ramdisk.addr + ramdisk.size).into(),
            Size2MiB::SIZE,
        )))
        .unwrap(),
    )
}

pub fn encryption() -> MemoryEncryption {
    // Should we set the C-bit (encrypted memory for SEV)? For now, let's assume
    // it's bit 51.
    if get_sev_status().unwrap_or(SevStatus::empty()).contains(SevStatus::SEV_ENABLED) {
        MemoryEncryption::Encrypted(ENCRYPTED_BIT_POSITION)
    } else {
        MemoryEncryption::NoEncryption
    }
}

/// Creates the initial page tables used by the kernel.
///
/// The memory layout we follow is largely based on the Linux layout
/// (<https://www.kernel.org/doc/Documentation/x86/x86_64/mm.txt>):
///
/// | Start address       |  Offset  | End address         |  Size   | Description                 |
/// |---------------------|----------|---------------------|---------|-----------------------------|
/// | 0000_0000_0000_0000 |     0    | 0000_7FFF_FFFF_FFFF |  128 TB | User space                  |
/// | 0000_8000_0000_0000 |  +128 TB | FFFF_7FFF_FFFF_FFFF |   16 EB | Non-canonical addresses, up |
/// |                     |          |                     |         | to -128 TB                  |
/// | FFFF_8000_0000_0000 |  -128 TB | FFFF_87FF_FFFF_FFFF |    8 TB | ... unused hole             |
/// | FFFF_8800_0000_0000 |  -120 TB | FFFF_881F_FFFF_FFFF |  128 GB | direct mapping of all       |
/// |                     |          |                     |         | physical memory             |
/// | FFFF_8820_0000_0000 | ~-120 TB | FFFF_FFFF_7FFF_FFFF | ~120 TB | ... unused hole             |
/// | FFFF_FFFF_8000_0000 |    -2 GB | FFFF_FFFF_FFFF_FFFF |    2 GB | Kernel code                 |
pub fn initial_pml4(program_headers: &[ProgramHeader]) -> Result<PhysFrame, &'static str> {
    // Safety: this expects the frame allocator to be initialized and the memory
    // region it's handing memory out of to be identity mapped. This is true for
    // the lower 2 GiB after we boot. This reference will no longer be valid
    // after we reload the page tables!
    let pml4_frame: PhysFrame<Size4KiB> =
        FRAME_ALLOCATOR.lock().allocate_frame().ok_or("couldn't allocate a frame for PML4")?;
    let pml4 = unsafe { &mut *(pml4_frame.start_address().as_u64() as *mut PageTable) };
    pml4.zero();

    // Populate all the kernel space entries of the level 4 page table. This means
    // that these entries should never change, memory allocation will happen on
    // lower level page tables. This is done to permit the kernel to switch
    // between different level 4 page tables in the future. All page tables that
    // include these mappings will point to the same lower level page tables /
    // memory in kernel space.
    {
        let mut fa = FRAME_ALLOCATOR.lock();
        for entry in pml4.iter_mut().skip(256) {
            let pml3_frame: PhysFrame<Size4KiB> =
                fa.allocate_frame().ok_or("couldn't allocate a frame for PML3")?;
            let pml3 = unsafe { &mut *(pml3_frame.start_address().as_u64() as *mut PageTable) };
            pml3.zero();
            entry.set_frame(pml3_frame, PageTableFlags::PRESENT.into());
        }
    };

    let mut page_table = EncryptedPageTable::new(pml4, VirtAddr::new(0), encryption());

    // Safety: these operations are safe as they're not done on active page tables.
    unsafe {
        // Create a direct map for all physical memory, marking it NO_EXECUTE. The size
        // (128 GB) has been chosen go coincide with the amout of memory our
        // frame allocator can track.
        page_tables::create_offset_map(
            PhysFrame::<Size2MiB>::range(
                PhysFrame::from_start_address(PhysAddr::new(0x00_0000_0000)).unwrap(),
                PhysFrame::from_start_address(PhysAddr::new(0x20_0000_0000)).unwrap(),
            ),
            DIRECT_MAPPING_OFFSET,
            PageTableFlags::PRESENT
                | PageTableFlags::GLOBAL
                | PageTableFlags::WRITABLE
                | PageTableFlags::NO_EXECUTE
                | PageTableFlags::ENCRYPTED,
            &mut page_table,
        )
        .map_err(|_| "couldn't set up paging for physical memory")?;

        // Mapping for the kernel itself in the upper -2G of memory, based on the
        // mappings (and permissions) in the program header.
        page_tables::create_kernel_map(program_headers, &mut page_table)
            .map_err(|_| "couldn't set up paging for the kernel")?;
    }

    Ok(pml4_frame)
}

/// Allocates memory usable as a stack.
///
/// The stack will be one page (2 MiB) in size, will be allocated in the
/// VMA_ALLOCATOR area, and will consume two pages: one as a unmapped stack
/// guard (so that we'd get a page fault if we blow the stack), and one backed
/// by a physical frame as the actual stack.
///
/// The return address is usable as the stack pointer; that is, it points to the
/// end of the allocated stack page.
pub fn allocate_stack() -> VirtAddr {
    // Of the two pages we allocate, the first will be the stack guard page, and the
    // second will be the actual stack.
    let pages = VMA_ALLOCATOR
        .lock()
        .allocate(2)
        .expect("unable to allocate virtual memory for syscall stack");
    let frame = FRAME_ALLOCATOR
        .lock()
        .allocate_frame()
        .expect("unable to allocate physical memory for syscall stack");
    let stack_page = pages.start + 1;
    unsafe {
        PAGE_TABLES
            .lock()
            .get()
            .unwrap()
            .map_to_with_table_flags(
                stack_page,
                frame,
                PageTableFlags::GLOBAL
                    | PageTableFlags::PRESENT
                    | PageTableFlags::ENCRYPTED
                    | PageTableFlags::NO_EXECUTE
                    | PageTableFlags::WRITABLE,
                PageTableFlags::ENCRYPTED | PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
            )
            .expect("failed to update page tables for syscall stack")
            .flush();
    };

    (stack_page + 1).start_address()
}
