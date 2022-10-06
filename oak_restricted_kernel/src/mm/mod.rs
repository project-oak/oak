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
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use x86_64::{
    addr::{align_down, align_up},
    registers::control::{Cr3, Cr3Flags},
    structures::paging::{
        FrameAllocator, OffsetPageTable, PageSize, PageTable, PageTableFlags, PhysFrame, Size2MiB,
        Size4KiB,
    },
    PhysAddr, VirtAddr,
};

mod bitmap_frame_allocator;
pub mod frame_allocator;
mod page_tables;

pub fn init<const N: usize>(
    memory_map: &[BootE820Entry],
    program_headers: &[ProgramHeader],
) -> frame_allocator::PhysicalMemoryAllocator<N> {
    // This assumes all memory is in the lower end of the address space.
    let mut alloc = frame_allocator::PhysicalMemoryAllocator::new(PhysFrame::range_inclusive(
        PhysFrame::from_start_address(PhysAddr::new(0x0)).unwrap(),
        // N u64-s * 64 frames per u64 * 2 MiB per frame
        PhysFrame::from_start_address(PhysAddr::new((N as u64 * 64 - 1) * Size2MiB::SIZE)).unwrap(),
    ));

    /* Step 1: mark all RAM as available (event though it may contain data!) */
    memory_map
        .iter()
        .inspect(|e| {
            info!(
                "E820 entry: [{:#018x}..{:#018x}) ({}), type {}",
                e.addr(),
                e.addr() + e.size(),
                e.size(),
                e.entry_type()
            );
        })
        .filter(|e| e.entry_type() == E820EntryType::RAM)
        .map(|e| {
            // Clip both ends, if necessary, to make sure that we are aligned with 2 MiB pages.
            (
                PhysAddr::new(align_up(e.addr() as u64, Size2MiB::SIZE)),
                PhysAddr::new(align_down((e.addr() + e.size()) as u64, Size2MiB::SIZE)),
            )
        })
        .filter(|(start, limit)| limit > start)
        .map(|(start, limit)| {
            // Safety: align_down/align_up guarantees we're aligned to 2 MiB boundaries,
            // and we know there's _something_ in the memory range.
            PhysFrame::range_inclusive(
                PhysFrame::from_start_address(start).unwrap(),
                PhysFrame::from_start_address(limit).unwrap() - 1,
            )
        })
        .for_each(|range| alloc.mark_valid(range, true));

    // Step 2: mark known in-use regions as not available.

    // First, leave out the first 2 MiB as there be dragons (and bootloader data structures)
    alloc.mark_valid(
        PhysFrame::range_inclusive(
            PhysFrame::from_start_address(PhysAddr::new(0x0)).unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(0x0)).unwrap(),
        ),
        false,
    );

    // Second, mark every `PT_LOAD` section from the phdrs as used.
    program_headers
        .iter()
        .filter(|phdr| phdr.p_type == PT_LOAD)
        .map(|phdr| {
            // Align the physical addresses to 2 MiB boundaries, making them larger if necessary.
            PhysFrame::range_inclusive(
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
                "marking [{:#018x}..{:#018x}] as reserved",
                range.start.start_address().as_u64(),
                range.end.start_address().as_u64() + range.end.size() - 1
            );
            alloc.mark_valid(range, false)
        });

    alloc
}

/// Initializes the page tables used by the kernel.
///
/// The memory layout we follow is largely based on the Linux layout
/// (<https://www.kernel.org/doc/Documentation/x86/x86_64/mm.txt>):
///
/// | Start address       | Offset  | End address         | Size   | Description                 |
/// |---------------------|---------|---------------------|--------|-----------------------------|
/// | 0000_0000_0000_0000 |    0    | 0000_7FFF_FFFF_FFFF | 128 TB | User space                  |
/// | 0000_8000_0000_0000 | +128 TB | FFFF_7FFF_FFFF_FFFF |  16 EB | Non-canonical addresses, up |
/// |                     |         |                     |        | to -128 TB                  |
/// | FFFF_8000_0000_0000 | -128 TB | FFFF_FFFF_7FFF_FFFF |~128 TB | ... unused hole             |
/// | FFFF_FFFF_8000_0000 |   -2 GB | FFFF_FFFF_FFFF_FFFF |   2 GB | Kernel code                 |
pub fn init_paging<A: FrameAllocator<Size4KiB> + ?Sized>(
    frame_allocator: &mut A,
) -> Result<(), &'static str> {
    // Safety: this expects the frame allocator to be initialized and the memory region it's handing
    // memory out of to be identity mapped. This is true for the lower 2 GiB after we boot.
    let pml4_frame = frame_allocator
        .allocate_frame()
        .ok_or("Could not allocate a frame for PML4")?;
    let pml4 = unsafe { &mut *(pml4_frame.start_address().as_u64() as *mut PageTable) };
    pml4.zero();

    // Safety: these page tables are unused (for now) and we have identity mapping for the lowest 2
    // GiB of memory.
    let mut page_table = unsafe { OffsetPageTable::new(pml4, VirtAddr::new(0)) };

    // Safety: these operations are safe as they're not done on active page tables.
    unsafe {
        // First, set up identity mapping for the lower 4 GiB of memory.
        // Once we've moved the kernel heap to the kernel memory, and figured out what to do with
        // MMIO, we should remove this completely.
        page_tables::create_offset_map(
            PhysFrame::range(
                PhysFrame::from_start_address(PhysAddr::new(0x0_0000_0000)).unwrap(),
                PhysFrame::from_start_address(PhysAddr::new(0x1_0000_0000)).unwrap(),
            ),
            VirtAddr::new(0x0000_0000),
            PageTableFlags::PRESENT | PageTableFlags::GLOBAL | PageTableFlags::WRITABLE,
            &mut page_table,
            frame_allocator,
        )
        .map_err(|_| "Failed to set up paging for [0..4GiB)")?;

        // Mapping for the kernel itself. In the future we should be more clever and only map
        // sections based on the ELF header with the correct permissions, but for now, all of the
        // memory will be writable and executable.
        page_tables::create_offset_map(
            PhysFrame::range(
                PhysFrame::from_start_address(PhysAddr::new(0x0000_0000)).unwrap(),
                PhysFrame::from_start_address(PhysAddr::new(0x8000_0000)).unwrap(),
            ),
            VirtAddr::new(0xFFFF_FFFF_8000_0000),
            PageTableFlags::PRESENT | PageTableFlags::GLOBAL | PageTableFlags::WRITABLE,
            &mut page_table,
            frame_allocator,
        )
        .map_err(|_| "Failed to set up paging for [-2GiB..MAX)")?;
    }

    // Safety: the new page tables keep the identity mapping at -2GB intact, so it's safe to load
    // the new page tables.
    unsafe {
        Cr3::write(pml4_frame, Cr3Flags::empty());
    }
    Ok(())
}
