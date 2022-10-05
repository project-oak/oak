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

use x86_64::{
    structures::paging::{
        frame::PhysFrameRange, mapper::MapToError, FrameAllocator, Mapper, Page, PageTableFlags,
        Size2MiB, Size4KiB,
    },
    VirtAddr,
};

pub unsafe fn create_offset_map<A: FrameAllocator<Size4KiB> + ?Sized, M: Mapper<Size2MiB>>(
    range: PhysFrameRange<Size2MiB>,
    offset: VirtAddr,
    flags: PageTableFlags,
    mapper: &mut M,
    frame_allocator: &mut A,
) -> Result<(), MapToError<Size2MiB>> {
    for frame in range {
        mapper
            .map_to_with_table_flags(
                Page::<Size2MiB>::from_start_address(offset + frame.start_address().as_u64())
                    .unwrap(),
                frame,
                flags,
                PageTableFlags::PRESENT | PageTableFlags::GLOBAL | PageTableFlags::WRITABLE,
                frame_allocator,
            )?
            .ignore();
    }
    Ok(())
}
