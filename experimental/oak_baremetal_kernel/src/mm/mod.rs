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
) -> frame_allocator::PhysicalMemoryAllocator<N> {
    // This assumes all memory is in the lower end of the address space.
    let mut alloc = frame_allocator::PhysicalMemoryAllocator::new(PhysFrame::range_inclusive(
        PhysFrame::from_start_address(PhysAddr::new(0x0)).unwrap(),
        // N u64-s * 64 frames per u64 * 2 MiB per frame
        PhysFrame::from_start_address(PhysAddr::new((N as u64 * 64 - 1) * Size2MiB::SIZE)).unwrap(),
    ));

    memory_map
        .iter()
        .inspect(|e| {
            info!(
                "E820 entry: [{:#016x}..{:#016x}) ({}), type {}",
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

    alloc
}
