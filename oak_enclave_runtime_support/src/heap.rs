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

//! no_std compatible allocators.

use core::{
    alloc::{GlobalAlloc, Layout},
    ops::Deref,
    ptr::NonNull,
};

use oak_restricted_kernel_interface::syscalls::{MmapFlags, MmapProtection};
use rlsf::{FlexSource, FlexTlsf};
use spinning_top::Spinlock;

struct Source {}

impl Source {
    // Restricted Kernel deals in 2 MiB pages, so that's what we use to request
    // memory.
    const PAGE_SIZE: usize = 0x20_0000usize;
}

unsafe impl FlexSource for Source {
    unsafe fn alloc(&mut self, min_size: usize) -> Option<NonNull<[u8]>> {
        // Ensure that we're allocating page-sized chunks of memory.
        let size = if min_size % Self::PAGE_SIZE != 0 {
            Self::PAGE_SIZE * ((min_size / Self::PAGE_SIZE) + 1)
        } else {
            min_size
        };

        oak_restricted_kernel_interface::syscall::mmap(
            // TODO(#3864): One we start compiling C++ applications internally using the Oak
            // Toolchain, we won't need to manually separate Rust and C++ heaps.
            Some(0x100_0000_0000 as *const core::ffi::c_void),
            size.try_into().ok()?,
            MmapProtection::PROT_READ | MmapProtection::PROT_WRITE,
            MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE,
            -1,
            0,
        )
        .map(|r| NonNull::new(r))
        .ok()
        .flatten()
    }

    fn min_align(&self) -> usize {
        Self::PAGE_SIZE
    }
}

/// Heap implementation that asks Restricted Kernel for more memory when
/// allocations fail.
///
/// We don't implement a heap allocation algorithm ourselves, but rather wrap a
/// real heap implementation; all allocations (and deallocations) are delegated
/// to the real heap implementation. When an allocation fails, we ask Restricted
/// Kernel for more memory and increase the size of the underlying heap, hoping
/// that eventually the allocation will succeed (or the machine runs out
/// memory).
pub struct GrowableHeap {
    /// Underlying heap implementation.
    heap: FlexTlsf<Source, usize, usize, { usize::BITS as usize }, { usize::BITS as usize }>,
}

impl GrowableHeap {
    pub const fn empty() -> Self {
        Self { heap: FlexTlsf::new(Source {}) }
    }

    #[allow(clippy::result_unit_err)]
    pub fn allocate(&mut self, layout: Layout) -> Result<NonNull<u8>, ()> {
        self.heap
            .allocate(layout)
            .ok_or_else(|| log::error!("failed to allocate memory with layout: {:?}", layout))
    }

    /// # Safety
    ///
    ///  - `ptr` must denote a memory block previously allocated via `self`.
    ///  - The memory block must have been allocated with the same alignment
    ///    ([`Layout::align`]) as `align`.
    pub unsafe fn deallocate(&mut self, ptr: NonNull<u8>, align: usize) {
        unsafe { self.heap.deallocate(ptr, align) }
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
        self.0.lock().allocate(layout).map(NonNull::as_ptr).unwrap_or(core::ptr::null_mut())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: core::alloc::Layout) {
        unsafe {
            self.0.lock().deallocate(NonNull::new_unchecked(ptr), layout.align());
        }
    }
}
