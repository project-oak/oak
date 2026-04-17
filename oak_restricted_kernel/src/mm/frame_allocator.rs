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
    PhysAddr,
    structures::paging::{
        FrameAllocator, FrameDeallocator, PageSize, PhysFrame, Size2MiB, Size4KiB,
        frame::PhysFrameRange,
    },
};

use super::bitmap_frame_allocator::BitmapAllocator;

/// Allocator to track physical memory frames.
///
/// The basic unit we track is a 2 MiB frame. If necessary, we will take one 2
/// MiB frame and break it into smaller, 4 KiB frames to satisfy demand.
///
/// The parameter N needs to be set to the number of u64-s required to track the
/// physical memory in a bitmap. For example, if we want to track 128 GiB of
/// memory, that means 128Gi/2Mi = 65Ki frames, which in turn means we need
/// 65Ki/64 = 1Ki u64-s (or: 1Ki * 8 = 8 KiB of memory).
pub struct PhysicalMemoryAllocator<const N: usize> {
    /// Allocator for 2 MiB frames.
    large_frames: BitmapAllocator<Size2MiB, N>,
    /// Allocator for 4 KiB frames.
    ///
    /// When first asked for a 4K frame, we take one 2 MiB frame to hand out as
    /// 4 KiB frames; that gives us 512 4K frames to hand out. Thus, the
    /// allocator bitmap needs to be 512/64 = 8 u64-s, or 64 B.
    small_frames: Option<BitmapAllocator<Size4KiB, 8>>,
}

impl<const N: usize> PhysicalMemoryAllocator<N> {
    /// Assumes valid physical memory ranges from [0 ... N * 64 *
    /// Size2MiB::SIZE].
    pub const fn new() -> Self {
        // Safety: we have to resort to `unsafe` as we need to call the const fn-s, but
        // both addresses are definitely Size2MiB::SIZE-aligned, so these
        // operations are safe.
        Self::new_range(PhysFrame::range(
            unsafe { PhysFrame::from_start_address_unchecked(PhysAddr::zero()) },
            // N u64-s * 64 frames per u64 * 2 MiB per frame
            unsafe {
                PhysFrame::from_start_address_unchecked(PhysAddr::new(
                    N as u64 * 64 * Size2MiB::SIZE,
                ))
            },
        ))
    }

    pub const fn new_range(range: PhysFrameRange<Size2MiB>) -> Self {
        PhysicalMemoryAllocator { large_frames: BitmapAllocator::new(range), small_frames: None }
    }

    pub fn mark_valid(&mut self, range: PhysFrameRange<Size2MiB>, valid: bool) {
        self.large_frames.mark_valid(range, valid)
    }

    pub fn largest_available(&mut self) -> Option<PhysFrameRange<Size2MiB>> {
        self.large_frames.largest_available()
    }

    /// Allocate `num` contiguous 2 MiB pages.
    ///
    /// Returns the frame range if a contiguous range of sufficient size was
    /// available; the memory is marked as allocated before returning.
    pub fn allocate_contiguous(&mut self, num: usize) -> Option<PhysFrameRange<Size2MiB>> {
        self.large_frames.allocate_contiguous(num)
    }

    /// Returns the number of valid 2 MiB and 4 KiB frames.
    pub fn num_valid_frames(&self) -> (usize, usize) {
        (
            self.large_frames.num_valid(),
            self.small_frames.as_ref().map_or(0, |frames| frames.num_valid()),
        )
    }

    /// Returns the number of allocated 2 MiB and 4 KiB frames.
    pub fn num_allocated_frames(&self) -> (usize, usize) {
        (
            self.large_frames.num_allocated(),
            self.small_frames.as_ref().map_or(0, |frames| frames.num_allocated()),
        )
    }
}

impl<const N: usize> Default for PhysicalMemoryAllocator<N> {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl<const N: usize> FrameAllocator<Size2MiB> for PhysicalMemoryAllocator<N> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<Size2MiB>> {
        self.large_frames.allocate_frame()
    }
}

impl<const N: usize> FrameDeallocator<Size2MiB> for PhysicalMemoryAllocator<N> {
    unsafe fn deallocate_frame(&mut self, frame: PhysFrame<Size2MiB>) {
        unsafe {
            self.large_frames.deallocate_frame(frame);
        }
    }
}

unsafe impl<const N: usize> FrameAllocator<Size4KiB> for PhysicalMemoryAllocator<N> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<Size4KiB>> {
        let allocator = self.small_frames.get_or_insert_with(|| {
            let frame = self.large_frames.allocate_frame().unwrap();
            // Safety: the frame we get from the 2MiB allocator is aligned to 2 MiB, which
            // means it's by definition aligned to 4K as well.
            let range = PhysFrame::range(
                PhysFrame::from_start_address(frame.start_address()).unwrap(),
                PhysFrame::from_start_address(frame.start_address() + frame.size()).unwrap(),
            );
            let mut alloc = BitmapAllocator::new(range);
            alloc.mark_valid(range, true);
            alloc
        });
        allocator.allocate_frame()
    }
}

impl<const N: usize> FrameDeallocator<Size4KiB> for PhysicalMemoryAllocator<N> {
    unsafe fn deallocate_frame(&mut self, frame: PhysFrame<Size4KiB>) {
        unsafe {
            self.small_frames.as_mut().unwrap().deallocate_frame(frame);
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use super::*;

    fn create_frame(start: u64) -> PhysFrame<Size2MiB> {
        PhysFrame::from_start_address(PhysAddr::new(start)).unwrap()
    }

    fn create_frame_range(start: u64, end: u64) -> PhysFrameRange<Size2MiB> {
        PhysFrame::range(create_frame(start), create_frame(end))
    }

    #[test]
    fn simple_allocator() {
        let mut allocator =
            PhysicalMemoryAllocator::<1>::new_range(create_frame_range(0, 2 * Size2MiB::SIZE));
        allocator.mark_valid(create_frame_range(0, 2 * Size2MiB::SIZE), true);
        (&mut allocator as &mut dyn FrameAllocator<Size2MiB>).allocate_frame().unwrap();
        (&mut allocator as &mut dyn FrameAllocator<Size4KiB>).allocate_frame().unwrap();
    }

    #[test]
    fn fill_small_frames() {
        let mut allocator =
            PhysicalMemoryAllocator::<1>::new_range(create_frame_range(0, Size2MiB::SIZE));
        allocator.mark_valid(create_frame_range(0, Size2MiB::SIZE), true);
        let alloc_ref = &mut allocator as &mut dyn FrameAllocator<Size4KiB>;
        // 512 allocations should succeed (512 * 4K = 2M)
        for _ in 0..512 {
            alloc_ref.allocate_frame().unwrap();
        }
        // and the next one shouldn't, as we've filled the page.
        assert_eq!(None, alloc_ref.allocate_frame());
    }
}
