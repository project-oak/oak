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

use core::{
    alloc::{GlobalAlloc, Layout},
    ffi::c_void,
    ops::Deref,
    ptr::NonNull,
};
use linked_list_allocator::Heap;
use oak_restricted_kernel_interface::syscalls::{MmapFlags, MmapProtection};
use spinning_top::Spinlock;

/// Heap implementation that asks Restricted Kernel for more memory when allocations fail.
///
/// We don't implement a heap allocation algorithm ourselves, but rather wrap a real heap
/// implementation; all allocations (and deallocations) are delegated to the real heap
/// implementation. When an allocation fails, we ask Restricted Kernel for more memory and increase
/// the size of the underlying heap, hoping that eventually the allocation will succeed (or the
/// machine runs out memory).
pub struct GrowableHeap {
    /// Underlying heap implementation.
    heap: Heap,

    /// Address of the base of the heap.
    base: Option<usize>,

    /// Address of the next virtual memory page to use for the heap.
    cursor: Option<usize>,
}

impl GrowableHeap {
    // Restricted Kernel deals in 2 MiB pages, so that's what we use to request memory.
    const PAGE_SIZE: usize = 0x20_0000usize;

    pub const fn empty() -> Self {
        Self {
            heap: Heap::empty(),
            base: None,
            cursor: None,
        }
    }

    pub unsafe fn init(&mut self) {
        // Get the first PAGE_SIZE MiB of memory for the heap.
        self.extend(1).unwrap();

        self.heap
            .init(self.base.unwrap() as *mut u8, Self::PAGE_SIZE);
    }

    /// Extends the current pool of memory by some number of pages.
    fn extend(&mut self, pages: usize) -> Result<(), &'static str> {
        if pages == 0 {
            return Ok(());
        }

        // If this is the first allocation, we don't want MAP_FIXED; however, for every consecutive
        // allocation, we want it to come immediately after the initial allocation so we need
        // MAP_FIXED.
        let flags = MmapFlags::MAP_ANONYMOUS
            | MmapFlags::MAP_PRIVATE
            | self
                .cursor
                .map_or_else(MmapFlags::empty, |_| MmapFlags::MAP_FIXED);

        let mem = oak_restricted_kernel_api::syscall::mmap(
            self.cursor.map(|x| x as *const c_void),
            (pages * Self::PAGE_SIZE) as isize,
            MmapProtection::PROT_READ | MmapProtection::PROT_WRITE,
            flags,
            -1,
            0,
        )
        .map_err(|_| "failed to acquire memory")?;

        // Move the cursor to the next unallocated page.
        self.cursor = Some(mem.as_ptr() as usize + (pages * Self::PAGE_SIZE));
        self.base.get_or_insert(mem.as_ptr() as usize);

        Ok(())
    }

    pub fn allocate_first_fit(&mut self, layout: Layout) -> Result<NonNull<u8>, ()> {
        // Try allocating the data structure; if the allocation fails, grow the heap and try again
        // until we succeed (or until we can't extend ourselves any further)
        // We extend the heap by powers of two until the allocation succeeds; this can be
        // inefficient, but will converge faster than just adding one page at a time until the data
        // structure fits.
        for pages in (0..).map(|n| 2usize.pow(n)) {
            match self.heap.allocate_first_fit(layout) {
                Ok(ptr) => return Ok(ptr),
                Err(()) => {
                    self.extend(pages).map_err(|err| log::error!("{}", err))?;
                    // Safety: this is safe as we've just mapped page(s) for the heap.
                    unsafe { self.heap.extend(pages * Self::PAGE_SIZE) };
                }
            }
        }

        unreachable!("allocation loop did not run even once");
    }

    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, layout: Layout) {
        self.heap.deallocate(ptr, layout)
    }
}

/// Thread-safe version of GrowableHeap, above, usable as a global allocator.
pub struct LockedGrowableHeap(Spinlock<GrowableHeap>);

impl LockedGrowableHeap {
    pub const fn empty() -> Self {
        Self(Spinlock::new(GrowableHeap::empty()))
    }
}

impl Deref for LockedGrowableHeap {
    type Target = Spinlock<GrowableHeap>;

    fn deref(&self) -> &Spinlock<GrowableHeap> {
        &self.0
    }
}

unsafe impl GlobalAlloc for LockedGrowableHeap {
    unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
        self.0
            .lock()
            .allocate_first_fit(layout)
            .ok()
            .map_or(core::ptr::null_mut(), |allocation| allocation.as_ptr())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        self.0
            .lock()
            .deallocate(NonNull::new_unchecked(ptr), layout)
    }
}
