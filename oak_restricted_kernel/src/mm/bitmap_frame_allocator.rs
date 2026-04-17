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

use core::ops::{BitAnd, Not};

use bitvec::{order::Lsb0, prelude::BitArray};
use x86_64::structures::paging::{
    FrameAllocator, FrameDeallocator, PhysFrame, frame::PhysFrameRange, page::PageSize,
};

/// Basic frame allocator implementation that keeps track of PageSize-sized
/// chunks of contiguous memory with a bitmap.
///
/// This implementation tracks memory using two bitmaps:
///   - `valid`, which tracks whether a frame can be allocated at all (not all
///     physical frames are usable memory)
///   - `allocated`, which tracks whether a frame is currently allocated or not.
///
/// A frame can be in one of three states:
///  valid = 0, allocated = _ -- the allocator will never hand out said frame.
///  valid = 1, allocated = 0 -- the frame is eligible for allocation.
///  valid = 1, allocated = 1 -- the frame is currently in use.
///
/// The BitmapAllocator itself does not use memory allocation (no heap is
/// required), but rather expects that the const parameter N is set to the exact
/// number of u64-s required to construct a bitmap covering the memory range.
/// (In container-ish terms, N specifies the capacity of the allocator, which
/// can not be resized.)
#[derive(Debug)]
pub(crate) struct BitmapAllocator<S: PageSize, const N: usize> {
    allocated: BitArray<[u64; N], Lsb0>,
    valid: BitArray<[u64; N], Lsb0>,
    range: PhysFrameRange<S>,
}

impl<S: PageSize, const N: usize> BitmapAllocator<S, N> {
    /// Creates a new bitmap allocator for a physical frame range.
    /// Panics if N does not match the number of u64-s required to track all
    /// frames in that range. Initially, the allocator will mark the whole
    /// range as invalid.
    pub const fn new(range: PhysFrameRange<S>) -> Self {
        // Unfortunately there doesn't seem to be a way to hoist this to the type
        // system. We also have to crudely reimplement `range.count()` here as
        // `count()` is not a const fn.
        let num_frames =
            (range.end.start_address().as_u64() - range.start.start_address().as_u64()) / S::SIZE;
        let expected = bitvec::mem::elts::<u64>(num_frames as usize);
        if expected != N {
            panic!("BitmapAllocator bitmap size does not match FrameRange size",);
        }

        Self { allocated: BitArray::ZERO, valid: BitArray::ZERO, range }
    }

    /// Marks a region of memory as either valid or invalid.
    ///
    /// Allocations can happen only from regions that are valid. This method
    /// does not check whether any allocations have been made from regions
    /// to be marked as invalid, and panics if the range is outside the
    /// range of the allocator.
    pub fn mark_valid(&mut self, range: PhysFrameRange<S>, valid: bool) {
        if let (Some(start), Some(end)) = (self.frame_idx(range.start), self.frame_idx(range.end)) {
            self.valid.get_mut(start..end).unwrap().fill(valid);
        } else {
            panic!(
                "Can't mark validity for frame range that's outside our range; our range: {:?}, frame range: {:?}",
                self.range, range
            );
        }
    }

    /// Returns a BitArray where 1 denotes a frame that's eligible for
    /// allocation.
    ///
    /// This means that (a) the frame needs to be marked as valid and (b) the
    /// frame has not been allocated yet.
    fn available(&self) -> BitArray<[u64; N]> {
        self.valid.bitand(self.allocated.not())
    }

    /// Returns the largest contiguous section of unallocated memory.
    pub fn largest_available(&self) -> Option<PhysFrameRange<S>> {
        self.available()
            .iter_ones()
            // Identify streaks of zeroes: for example, 0100 will yield (0,0), (2,2), (2,3)
            .scan(None, |state, idx| {
                let start_idx = state.map_or_else(
                    || idx,
                    |(start_idx, end_idx)| if idx == end_idx + 1 { start_idx } else { idx },
                );
                *state = Some((start_idx, idx));
                Some((start_idx, idx))
            })
            .max_by_key(|(start_idx, end_idx)| end_idx - start_idx)
            .map(|(start_idx, end_idx)| {
                PhysFrame::range(self.frame(start_idx).unwrap(), self.frame(end_idx).unwrap() + 1)
            })
    }

    /// Tries to allocate a specific frame range in the range managed by the
    /// allocator.
    ///
    /// Returns the same frame range if the allocation was successful; None, if
    /// not.
    ///
    /// Panics if the frame is outside the bounds of memory that is managed by
    /// this allocator.
    pub fn allocate(&mut self, frame_range: PhysFrameRange<S>) -> Option<PhysFrameRange<S>> {
        if let (Some(start_idx), Some(end_idx)) =
            (self.frame_idx(frame_range.start), self.frame_idx(frame_range.end))
        {
            if self.available()[start_idx..end_idx].not_all() {
                return None;
            }
            self.allocated[start_idx..end_idx].fill(true);
            Some(frame_range)
        } else {
            panic!(
                "Can't allocate frame range that's outside our range; our range: {:?}, frame range: {:?}",
                self.range, frame_range
            );
        }
    }

    /// Attempts to allocate `num` contiguous physical frames.
    pub fn allocate_contiguous(&mut self, num: usize) -> Option<PhysFrameRange<S>> {
        let (start_idx, end_idx) = self
            .available()
            // split into overlapping views of length n
            .windows(num)
            // keep an index (the index of the first bit)
            .enumerate()
            // find us a window that's all 1-s
            .find(|(_, window)| window.all())
            .map(|(idx, _)| (idx, idx + num))?;

        // Safety: unwrapping these indexes is safe as we obtained them by indexing
        // valid entries in the map, so they shouldn't be outside the range.
        self.allocate(PhysFrame::range(
            self.frame(start_idx).unwrap(),
            self.frame(end_idx).unwrap(),
        ))
    }

    fn frame(&self, frame_idx: usize) -> Option<PhysFrame<S>> {
        if self.valid.len() <= frame_idx { None } else { Some(self.range.start + frame_idx as u64) }
    }

    fn frame_idx(&self, frame: PhysFrame<S>) -> Option<usize> {
        if frame < self.range.start || frame > self.range.end {
            None
        } else {
            Some(
                ((frame.start_address().as_u64() - self.range.start.start_address().as_u64())
                    / S::SIZE) as usize,
            )
        }
    }

    pub fn num_valid(&self) -> usize {
        self.valid.count_ones()
    }

    pub fn num_allocated(&self) -> usize {
        self.allocated.count_ones()
    }
}

unsafe impl<S: PageSize, const N: usize> FrameAllocator<S> for BitmapAllocator<S, N> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<S>> {
        let frame_idx = self.valid.bitand(self.allocated.not()).first_one()?;
        self.allocated.set(frame_idx, true);
        self.frame(frame_idx)
    }
}

impl<S: PageSize, const N: usize> FrameDeallocator<S> for BitmapAllocator<S, N> {
    unsafe fn deallocate_frame(&mut self, frame: PhysFrame<S>) {
        if let Some(frame_idx) = self.frame_idx(frame) {
            if !self.valid[frame_idx] {
                panic!("frame {:?} is not valid in this allocator", frame);
            }
            if !self.allocated[frame_idx] {
                panic!("frame {:?} was not allocated in this allocator", frame);
            }
            self.allocated.set(frame_idx, false);
        } else {
            panic!(
                "can't deallocate frame that's outside our range; our range: {:?}, frame: {:?}",
                self.range, frame
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{format, prelude::rust_2021::*, vec};

    use assertables::*;
    use x86_64::{PhysAddr, structures::paging::Size4KiB};

    use super::*;

    fn create_allocator<const N: usize>(start: u64, end: u64) -> BitmapAllocator<Size4KiB, N> {
        BitmapAllocator::<Size4KiB, N>::new(PhysFrame::range(
            PhysFrame::from_start_address(PhysAddr::new(start)).unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(end)).unwrap(),
        ))
    }

    fn create_frame(start: u64) -> PhysFrame<Size4KiB> {
        PhysFrame::from_start_address(PhysAddr::new(start)).unwrap()
    }

    fn create_frame_range(start: u64, end: u64) -> PhysFrameRange<Size4KiB> {
        PhysFrame::range(create_frame(start), create_frame(end))
    }

    #[test]
    fn silly_allocator_invalid() {
        let mut alloc = create_allocator::<1>(0x0000, 0x1000);
        // Nothing is valid yet.
        assert_eq!(None, alloc.allocate_frame());
    }

    #[test]
    fn silly_allocator_valid() {
        let mut alloc = create_allocator::<1>(0x0000, 0x1000);
        alloc.mark_valid(create_frame_range(0x0000, 0x1000), true);
        assert_eq!(1, alloc.num_valid());
        assert_eq!(0, alloc.num_allocated());
        assert_eq!(Some(create_frame(0x0000)), alloc.allocate_frame());
        assert_eq!(1, alloc.num_valid());
        assert_eq!(1, alloc.num_allocated());
    }

    #[should_panic]
    #[test]
    fn silly_allocator_invalid_size() {
        create_allocator::<0>(0x0000, 0x1000);
    }

    #[test]
    fn double_allocate() {
        let mut alloc = create_allocator::<1>(0x0000, 0x1000);
        alloc.mark_valid(create_frame_range(0x0000, 0x1000), true);
        assert_eq!(Some(create_frame(0x0000)), alloc.allocate_frame());
        assert_eq!(None, alloc.allocate_frame());
        assert_eq!(1, alloc.num_allocated());
    }

    #[test]
    fn new_allocator_success() {
        let expected_frames: Vec<PhysFrame<Size4KiB>> =
            (0..9).map(|x| create_frame(x * 0x1000)).collect();

        let mut alloc = create_allocator::<1>(0x0000, expected_frames.len() as u64 * 0x1000);
        alloc.mark_valid(create_frame_range(0x0000, expected_frames.len() as u64 * 0x1000), true);
        assert_eq!(9, alloc.num_valid());
        assert_eq!(0, alloc.num_allocated());

        let got_frames: Vec<PhysFrame<Size4KiB>> =
            (0..expected_frames.len()).map(|_| alloc.allocate_frame().unwrap()).collect();

        assert_set_eq!(expected_frames, got_frames);
        assert_eq!(None, alloc.allocate_frame());
        assert_eq!(9, alloc.num_allocated());
    }

    #[test]
    fn realloc() {
        let mut alloc = create_allocator::<1>(0x0000, 0x1000);
        alloc.mark_valid(create_frame_range(0x0000, 0x1000), true);
        assert_eq!(1, alloc.num_valid());
        assert_eq!(0, alloc.num_allocated());
        assert_eq!(Some(create_frame(0x0000)), alloc.allocate_frame());
        assert_eq!(None, alloc.allocate_frame());
        assert_eq!(1, alloc.num_allocated());
        unsafe {
            alloc.deallocate_frame(create_frame(0x0000));
        }
        assert_eq!(0, alloc.num_allocated());
        assert_eq!(Some(create_frame(0x0000)), alloc.allocate_frame());
        assert_eq!(None, alloc.allocate_frame());
        assert_eq!(1, alloc.num_allocated());
    }

    #[should_panic]
    #[test]
    fn dealloc_unallocated() {
        let mut alloc = create_allocator::<1>(0x0000, 0x1000);
        unsafe {
            alloc.deallocate_frame(create_frame(0x0000));
        }
    }

    #[should_panic]
    #[test]
    fn dealloc_outside_lo() {
        let mut alloc = create_allocator::<1>(0x1000, 0x2000);
        unsafe {
            alloc.deallocate_frame(create_frame(0x0000));
        }
    }

    #[should_panic]
    #[test]
    fn dealloc_outside_hi() {
        let mut alloc = create_allocator::<1>(0x1000, 0x2000);
        unsafe {
            alloc.deallocate_frame(create_frame(0x2000));
        }
    }

    #[test]
    fn alloc_hi() {
        let mut alloc = create_allocator::<1>(0x1000, 0x2000);
        alloc.mark_valid(create_frame_range(0x1000, 0x2000), true);
        assert_eq!(Some(create_frame(0x1000)), alloc.allocate_frame());
        assert_eq!(None, alloc.allocate_frame());
    }

    #[test]
    fn hole_in_validity() {
        let mut alloc = create_allocator::<1>(0x0000, 0x3000);
        let expected_frames = vec![create_frame(0x0000), create_frame(0x2000)];

        expected_frames
            .iter()
            .for_each(|frame| alloc.mark_valid(PhysFrame::range(*frame, *frame + 1), true));
        let got_frames: Vec<PhysFrame<Size4KiB>> =
            (0..expected_frames.len()).map(|_| alloc.allocate_frame().unwrap()).collect();
        assert_set_eq!(expected_frames, got_frames);
        assert_eq!(None, alloc.allocate_frame());
    }

    #[should_panic]
    #[test]
    fn valid_outside_range_lo() {
        let mut alloc = create_allocator::<1>(0x1000, 0x2000);
        alloc.mark_valid(create_frame_range(0x0000, 0x0000), true);
    }

    #[test]
    fn get_largest() {
        let mut alloc = create_allocator::<1>(0x0000, 0x4000);
        alloc.mark_valid(create_frame_range(0x0000, 0x4000), true);
        let range = alloc.largest_available().unwrap();
        assert_eq!(create_frame(0x0000), range.start);
        assert_eq!(create_frame(0x4000), range.end);
        alloc.mark_valid(create_frame_range(0x1000, 0x2000), false);
        let range = alloc.largest_available().unwrap();
        assert_eq!(create_frame(0x2000), range.start);
        assert_eq!(create_frame(0x4000), range.end);
    }

    #[test]
    fn test_allocate_specific_region() {
        let mut alloc = create_allocator::<1>(0x0000, 0x2000);
        alloc.mark_valid(create_frame_range(0x0000, 0x2000), true);
        alloc.allocate(create_frame_range(0x0000, 0x1000)).unwrap();
        assert_eq!(None, alloc.allocate(create_frame_range(0x0000, 0x1000)));
        assert_eq!(None, alloc.allocate(create_frame_range(0x0000, 0x2000)));
        assert_eq!(Some(create_frame(0x1000)), alloc.allocate_frame());
        assert_eq!(None, alloc.allocate(create_frame_range(0x0000, 0x2000)));
        assert_eq!(None, alloc.allocate(create_frame_range(0x1000, 0x2000)));
        assert_eq!(None, alloc.allocate_frame());
    }

    #[test]
    fn test_allocate_contiguous() {
        let mut alloc = create_allocator::<1>(0x0000, 0x3000);
        alloc.mark_valid(create_frame_range(0x0000, 0x3000), true);
        assert_eq!(None, alloc.allocate_contiguous(4));
        alloc.allocate_contiguous(2).unwrap();
        alloc.allocate_contiguous(1).unwrap();
        assert_eq!(None, alloc.allocate_contiguous(2));
        assert_eq!(None, alloc.allocate_frame());
    }
}
