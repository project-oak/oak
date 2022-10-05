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

use crate::boot::{E820Entry, E820EntryType};
use goblin::{elf32::program_header::PT_LOAD, elf64::program_header::ProgramHeader};
use log::info;
use x86_64::{
    addr::{align_down, align_up},
    structures::paging::{PageSize, PhysFrame, Size2MiB},
    PhysAddr,
};

mod bitmap_frame_allocator;
pub mod frame_allocator;

pub fn init<const N: usize, E: E820Entry>(
    memory_map: &[E],
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
