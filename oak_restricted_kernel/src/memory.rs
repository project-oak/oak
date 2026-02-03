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
    ops::Deref,
    ptr::NonNull,
};

use linked_list_allocator::{Heap, LockedHeap};
use log::info;
use spinning_top::Spinlock;
use x86_64::{
    VirtAddr,
    structures::paging::{
        FrameAllocator, Page, PageSize, PhysFrame, Size2MiB, mapper::FlagUpdateError,
        page::PageRange,
    },
};

use crate::{
    FRAME_ALLOCATOR, PAGE_TABLES,
    mm::{Mapper, PageTableFlags},
};

#[cfg(not(test))]
#[global_allocator]
static ALLOCATOR: LockedGrowableHeap = LockedGrowableHeap::empty();

#[cfg(test)]
static ALLOCATOR: LockedGrowableHeap = LockedGrowableHeap::empty();

/// Heap allocator that requests more physical memory as required.
struct GrowableHeap {
    /// Underlying heap allocator implementation.
    heap: Heap,

    /// Virtual address range available for the heap.
    base: Page<Size2MiB>,

    /// Non-inclusive limit of the heap: the last page of the heap.
    ///
    /// The heap will use [base, cursor) addresses in the virtual memory.
    available: PageRange<Size2MiB>,
}

impl GrowableHeap {
    pub const fn empty() -> Self {
        // Safety: zero is definitely aligned with a 2 MiB boundary.
        let zero_page = unsafe { Page::from_start_address_unchecked(VirtAddr::zero()) };
        Self { heap: Heap::empty(), base: zero_page, available: Page::range(zero_page, zero_page) }
    }

    /// Extends the current pool of memory by one 2 MiB page.
    fn extend(&mut self) -> Result<(), &'static str> {
        // We might want to do something more clever here, such as exponentially
        // increasing the number of frames we allocate. For now, let's just keep
        // extending by one frame.
        let frame: PhysFrame<Size2MiB> = FRAME_ALLOCATOR
            .lock()
            .allocate_frame()
            .ok_or("failed to allocate memory for kernel heap")?;
        let pt_guard = PAGE_TABLES.lock();
        let mapper = pt_guard.get().unwrap();

        // Safety: if the page is already mapped, then we'll get an error and thus we
        // won't overwrite any existing mappings, Otherwise, creating a new
        // mapping is safe as the memory is currently unused and thus there
        // should be no references to that memory.
        unsafe {
            mapper
                .map_to_with_table_flags(
                    self.available.next().ok_or("kernel heap exhausted")?,
                    frame,
                    PageTableFlags::PRESENT
                        | PageTableFlags::WRITABLE
                        | PageTableFlags::GLOBAL
                        | PageTableFlags::NO_EXECUTE
                        | PageTableFlags::HUGE_PAGE
                        | PageTableFlags::ENCRYPTED,
                    PageTableFlags::PRESENT
                        | PageTableFlags::WRITABLE
                        | PageTableFlags::NO_EXECUTE
                        | PageTableFlags::ENCRYPTED,
                )
                .map_err(|_| "unable to create page mapping for kernel heap")?
                .flush();
        }

        log::debug!(
            "Extending kernel heap to [{:#018x}..{:#018x}).",
            self.base.start_address().as_u64(),
            self.available.start.start_address().as_u64(),
        );
        Ok(())
    }

    pub unsafe fn init(&mut self, range: PageRange<Size2MiB>) {
        self.base = range.start;
        self.available = range;

        // Get the first 2 MiB of memory for the heap.
        self.extend().unwrap();

        unsafe {
            self.heap.init(self.base.start_address().as_mut_ptr(), Size2MiB::SIZE as usize);
        }
    }

    pub fn allocate_first_fit(&mut self, layout: Layout) -> Result<NonNull<u8>, ()> {
        // Try allocating the data structure; if the allocation fails, grow the heap and
        // try again until we succeed (or until we can't extend ourselves any
        // further)
        loop {
            match self.heap.allocate_first_fit(layout) {
                Ok(ptr) => return Ok(ptr),
                Err(()) => {
                    self.extend().map_err(|err| log::error!("{}", err))?;
                    // Safety: this is safe as we've just mapped a fresh 2 MiB page for the heap.
                    unsafe { self.heap.extend(Size2MiB::SIZE as usize) };
                }
            }
        }
    }

    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, layout: Layout) {
        unsafe {
            self.heap.deallocate(ptr, layout);
        }
    }
}

struct LockedGrowableHeap(Spinlock<GrowableHeap>);

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
        unsafe {
            self.0.lock().deallocate(NonNull::new_unchecked(ptr), layout);
        }
    }
}

/// Initializes the global allocator from the largest contiguous slice of
/// available memory.
///
/// Pointers to addresses in the memory area (or references to data contained
/// within the slice) must be considered invalid after calling this function, as
/// the allocator may overwrite the data at any point.
pub fn init_kernel_heap(range: PageRange<Size2MiB>) -> Result<(), &'static str> {
    // This is safe as we know the memory is available based on the e820 map.
    unsafe {
        ALLOCATOR.lock().init(range);
    }
    Ok(())
}

/// Initializes an allocator for guest-host communication on unencrypted memory.
///
/// # Safety
///
/// The caller has to guarantee that the page range is valid and not in use, as
/// we will change page table flags for pages in that range.
pub unsafe fn init_guest_host_heap<S: PageSize, M: Mapper<S>>(
    pages: PageRange<S>,
    mapper: &M,
) -> Result<LockedHeap, FlagUpdateError> {
    for page in pages {
        unsafe {
            mapper
                .update_flags(
                    page,
                    PageTableFlags::PRESENT
                        | PageTableFlags::WRITABLE
                        | PageTableFlags::GLOBAL
                        | PageTableFlags::NO_EXECUTE,
                )?
                .flush();
        }
    }

    info!(
        "Marking [{:#018x}..{:#018x}) for guest-host communication.",
        pages.start.start_address().as_u64(),
        pages.end.start_address().as_u64()
    );

    Ok(unsafe {
        LockedHeap::new(pages.start.start_address().as_mut_ptr(), pages.count() * S::SIZE as usize)
    })
}
