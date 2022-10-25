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

use goblin::elf64::program_header::{ProgramHeader, PF_W, PF_X, PT_LOAD};
use x86_64::{
    align_down, align_up,
    structures::paging::{
        frame::PhysFrameRange, mapper::MapToError, FrameAllocator, Page, PageSize, PhysFrame,
        Size2MiB, Size4KiB,
    },
    PhysAddr, VirtAddr,
};

use super::{Mapper, PageTableFlags};

/// Map a region of physical memory to a virtual address using 2 MiB pages.
///
/// ## Safety
///
/// There are many ways you can cause memory safety errors and undefined behaviour when creating
/// page mappings. See <Mapper::map_to_with_table_flags> for examples.
pub unsafe fn create_offset_map<S: PageSize, A: FrameAllocator<Size4KiB>, M: Mapper<S>>(
    range: PhysFrameRange<S>,
    offset: VirtAddr,
    flags: PageTableFlags,
    mapper: &mut M,
    frame_allocator: &mut A,
) -> Result<(), MapToError<S>> {
    for (i, frame) in range.enumerate() {
        // We don't set `PageTableFlags::GLOBAL` in `parent_table_flags` because Intel and AMD CPUs
        // behave differently (Intel ignores the `G` bit in parent page table entries, AMD ignores
        // it in lower entries _except_ PML4 and PML5); the `G` bit has semantic meaning only in the
        // lowest level of page tables.
        mapper
            .map_to_with_table_flags(
                Page::<S>::from_start_address(offset + i * (S::SIZE as usize)).unwrap(),
                frame,
                flags,
                PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::ENCRYPTED,
                frame_allocator,
            )?
            .ignore();
    }
    Ok(())
}

/// Maps the kernel memory ranges (ie. vaddr in last 2GB of memory), respecting section permissions.
///
/// Strictly speaking there's nothing int he ELF file that _requires_ sections to be page-aligned.
/// It's entirely possible to have a section with write privileges and a section with execute
/// privileges be on the same 4K page -- which would defeat the purpose of restricting the
/// permissions, as we'd have to go for the lowest common denominator and mark the pages both
/// writable and executable.
/// For now, calling this function fails if there is any overlap when using 4K pages.
///
/// We also create mappings only for sections with vaddr above 0xFFFF_FFFF_8000_0000, that is, for
/// the memory range where the kernel code should lie.
///
/// The mappings we create respect the `PF_W` and `PF_X` flags; there's no way how to map a page as
/// not readable (but still writable or executable), so `PF_R` is ignored.
///
/// Note that even if this function returns an error, the page map may have been partially updated.
///
/// # Safety
/// There are many ways you can cause memory safety errors and undefined behaviour when creating
/// page mappings. See <Mapper::map_to_with_table_flags> for examples.
///
/// `EferFlags::NO_EXECUTE_ENABLE` needs to be enabled before loading the page tables created by
/// this function.
pub unsafe fn create_kernel_map<
    A: FrameAllocator<Size4KiB>,
    M: Mapper<Size2MiB> + Mapper<Size4KiB>,
>(
    program_headers: &[ProgramHeader],
    mapper: &mut M,
    frame_allocator: &mut A,
) -> Result<(), MapToError<Size4KiB>> {
    program_headers
        .iter()
        .filter(|phdr| phdr.p_type == PT_LOAD && phdr.p_vaddr >= 0xFFFF_FFFF_8000_0000)
        .map(|phdr| {
            (
                PhysFrame::<Size4KiB>::range(
                    PhysFrame::from_start_address(PhysAddr::new(align_down(
                        phdr.p_paddr,
                        Size4KiB::SIZE,
                    )))
                    .unwrap(),
                    PhysFrame::from_start_address(PhysAddr::new(align_up(
                        phdr.p_paddr + phdr.p_memsz,
                        Size4KiB::SIZE,
                    )))
                    .unwrap(),
                ),
                VirtAddr::new(phdr.p_vaddr),
                /* It's not possible to mark a page not readable, so we ignore PF_R. */
                PageTableFlags::PRESENT
                    | PageTableFlags::GLOBAL
                    | PageTableFlags::ENCRYPTED
                    | if phdr.p_flags & PF_W > 0 {
                        PageTableFlags::WRITABLE
                    } else {
                        PageTableFlags::empty()
                    }
                    | if phdr.p_flags & PF_X == 0 {
                        PageTableFlags::NO_EXECUTE
                    } else {
                        PageTableFlags::empty()
                    },
            )
        })
        .try_for_each(|(range, offset, flags)| {
            create_offset_map(range, offset, flags, mapper, frame_allocator)
        })
}
