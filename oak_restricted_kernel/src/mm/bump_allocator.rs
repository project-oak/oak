//
// Copyright 2026 The Project Oak Authors
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
    alloc::{AllocError, Allocator, GlobalAlloc, Layout},
    ptr::NonNull,
};

use spinning_top::Spinlock;

struct Inner {
    base: usize,
    size: usize,
    index: usize,
}

/// A bump allocator for allocating memory from a contiguous memory region.
///
/// This allocator keeps all metadata (base address, total capacity, and current
/// allocation index) in private kernel memory (inside this struct), rather than
/// storing metadata (such as free list nodes or hole headers) in the allocated
/// memory region itself. This makes it suitable and safe for memory regions
/// that are shared with an untrusted host or hypervisor (e.g.
/// `GUEST_HOST_HEAP`), preventing metadata manipulation attacks by a malicious
/// hypervisor.
///
/// Deallocations are no-ops as bump allocators do not reclaim individual
/// memory allocations.
pub struct BumpAllocator {
    inner: Spinlock<Inner>,
}

impl BumpAllocator {
    /// Creates a new uninitialized `BumpAllocator`.
    ///
    /// Allocations from an uninitialized allocator will fail with `AllocError`.
    pub const fn uninit() -> Self {
        Self { inner: Spinlock::new(Inner { base: 0, size: 0, index: 0 }) }
    }

    /// Creates a new `BumpAllocator` covering the memory region `[base, base +
    /// size)`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the memory region `[base, base + size)` is
    /// valid, properly mapped, and that no other references exist to this
    /// memory region.
    pub unsafe fn new(base: *mut u8, size: usize) -> Self {
        Self { inner: Spinlock::new(Inner { base: base as usize, size, index: 0 }) }
    }

    /// Initializes an uninitialized `BumpAllocator` with a memory region.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the memory region `[base, base + size)` is
    /// valid, properly mapped, and that no other references exist to this
    /// memory region.
    pub unsafe fn init(&self, base: *mut u8, size: usize) {
        let mut inner = self.inner.lock();
        inner.base = base as usize;
        inner.size = size;
        inner.index = 0;
    }
}

impl Default for BumpAllocator {
    fn default() -> Self {
        Self::uninit()
    }
}

unsafe impl Allocator for BumpAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let mut inner = self.inner.lock();
        if inner.base == 0 || inner.size == 0 {
            return Err(AllocError);
        }

        let current_addr = inner.base.checked_add(inner.index).ok_or(AllocError)?;
        let align_mask = layout.align() - 1;
        let aligned_addr = (current_addr.checked_add(align_mask).ok_or(AllocError)?) & !align_mask;
        let end_addr = aligned_addr.checked_add(layout.size()).ok_or(AllocError)?;
        let base_end = inner.base.checked_add(inner.size).ok_or(AllocError)?;

        if end_addr > base_end {
            return Err(AllocError);
        }

        inner.index = end_addr - inner.base;

        let ptr = NonNull::new(aligned_addr as *mut u8).ok_or(AllocError)?;
        Ok(NonNull::slice_from_raw_parts(ptr, layout.size()))
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        // Bump allocator never deallocates.
    }
}

unsafe impl GlobalAlloc for BumpAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        self.allocate(layout)
            .ok()
            .map_or(core::ptr::null_mut(), |allocation| allocation.as_ptr() as *mut u8)
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {
        // Bump allocator never deallocates.
    }
}

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;
    use core::alloc::Layout;

    use super::*;

    #[test]
    fn uninit_allocator_fails() {
        let alloc = BumpAllocator::uninit();
        assert!(alloc.allocate(Layout::new::<u32>()).is_err());
    }

    #[test]
    fn simple_alloc() {
        let mut buffer = [0u8; 64];
        let alloc = unsafe { BumpAllocator::new(buffer.as_mut_ptr(), buffer.len()) };

        let val = Box::try_new_in(42u32, &alloc);
        assert!(val.is_ok());
        let val = val.unwrap();
        assert_eq!(*val, 42);
    }

    #[test]
    fn sequential_allocations() {
        let mut buffer = [0u8; 128];
        let alloc = unsafe { BumpAllocator::new(buffer.as_mut_ptr(), buffer.len()) };

        let b1 = Box::new_in(10u64, &alloc);
        let b2 = Box::new_in(20u64, &alloc);
        let b3 = Box::new_in(30u64, &alloc);

        assert_eq!(*b1, 10);
        assert_eq!(*b2, 20);
        assert_eq!(*b3, 30);
    }

    #[test]
    fn alignment_respected() {
        #[repr(align(64))]
        struct Aligned64 {
            value: u64,
        }

        let mut buffer = [0u8; 512];
        let alloc = unsafe { BumpAllocator::new(buffer.as_mut_ptr(), buffer.len()) };

        // Allocate a single byte first to misalign the cursor.
        let _byte = Box::new_in(1u8, &alloc);

        // Now allocate aligned struct.
        let aligned = Box::new_in(Aligned64 { value: 0x1234_5678 }, &alloc);
        assert_eq!((aligned.as_ref() as *const Aligned64 as usize) % 64, 0);
        assert_eq!(aligned.value, 0x1234_5678);
    }

    #[test]
    fn out_of_memory() {
        let mut buffer = [0u8; 16];
        let alloc = unsafe { BumpAllocator::new(buffer.as_mut_ptr(), buffer.len()) };

        let b1 = Box::try_new_in([0u8; 12], &alloc);
        assert!(b1.is_ok());

        // Not enough remaining space (only 4 bytes left for 8 bytes request).
        let b2 = Box::try_new_in([0u8; 8], &alloc);
        assert!(b2.is_err());
    }

    #[test]
    fn zero_sized_allocation() {
        let mut buffer = [0u8; 32];
        let alloc = unsafe { BumpAllocator::new(buffer.as_mut_ptr(), buffer.len()) };

        let zst = Box::try_new_in((), &alloc);
        assert!(zst.is_ok());
    }

    #[test]
    fn init_method() {
        let alloc = BumpAllocator::uninit();
        assert!(alloc.allocate(Layout::new::<u64>()).is_err());

        let mut buffer = [0u8; 64];
        unsafe { alloc.init(buffer.as_mut_ptr(), buffer.len()) };

        let val = Box::try_new_in(99u64, &alloc);
        assert!(val.is_ok());
        assert_eq!(*val.unwrap(), 99);
    }

    #[test]
    fn deallocate_is_noop() {
        let mut buffer = [0u8; 32];
        let alloc = unsafe { BumpAllocator::new(buffer.as_mut_ptr(), buffer.len()) };

        let b1 = Box::new_in(123u32, &alloc);
        drop(b1); // calls deallocate

        let b2 = Box::new_in(456u32, &alloc);
        assert_eq!(*b2, 456);
    }
}
