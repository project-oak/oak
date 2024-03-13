//
// Copyright 2023 The Project Oak Authors
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
    alloc::{AllocError, Allocator, Layout},
    mem::MaybeUninit,
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use spinning_top::Spinlock;
use x86_64::VirtAddr;

struct Inner<const N: usize> {
    index: AtomicUsize,
    storage: MaybeUninit<[u8; N]>,
}

impl<const N: usize> Inner<N> {
    const fn new() -> Self {
        Self { index: AtomicUsize::new(0), storage: MaybeUninit::uninit() }
    }
}

/// Basic bump allocator that never deallocates memory.
///
/// The algorithm is rather simple: we maintain an index into the buffer we
/// hold, that marks the high water mark (already allocated memory). Whenever a
/// request for memory comes in, me move the index forward by the padding
/// necessary to maintain proper alignment for the structure plus the
/// size of the structure.
///
/// We do not support deallocation, and there is no optimizations to pack the
/// allocations as efficiently as possible.
///
/// For stage0 uses these limitations are not an issue because (a) we use this
/// allocator to allocate data structures we expect to outlive stage0 and (b) we
/// allocate only a small number of data structures from it, so the padding
/// overhead is minimal.
pub struct BumpAllocator<const N: usize> {
    inner: Spinlock<Inner<N>>,
}

impl<const N: usize> BumpAllocator<N> {
    pub const fn uninit() -> Self {
        Self { inner: Spinlock::new(Inner::new()) }
    }
}

unsafe impl<const N: usize> Allocator for BumpAllocator<N> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let mut inner = self.inner.lock();
        let offset = inner.index.load(Ordering::Acquire);
        let storage_ptr = inner.storage.as_mut_ptr() as *mut u8;

        // We may need to allocate extra bytes to ensure proper alignment in memory.
        let align = if (storage_ptr as usize + offset) % layout.align() > 0 {
            layout.align() - ((storage_ptr as usize + offset) % layout.align())
        } else {
            0
        };

        if offset + align + layout.size() > N {
            // memory exhausted
            return Err(AllocError);
        }

        inner.index.fetch_add(align + layout.size(), Ordering::SeqCst);

        // Safety: we've reserved memory from [offset, offset + align + size) so this
        // will not exceed the bounds of `self.storage` and is not aliased.
        Ok(NonNull::slice_from_raw_parts(
            unsafe { NonNull::new_unchecked(storage_ptr.add(offset + align)) },
            layout.size(),
        ))
    }

    unsafe fn deallocate(&self, _: NonNull<u8>, _: Layout) {
        // Bump allocator never deallocates.
    }
}

pub fn init_global_allocator(e820_table: &[BootE820Entry]) {
    // Create the heap between 1MiB and 2MiB.
    let start = VirtAddr::new(0x100000);
    let size = 0x100000usize;
    let end = start + size as u64;

    // Check that this range is backed by physical memory.
    if !e820_table.iter().any(|entry| {
        entry.entry_type() == Some(E820EntryType::RAM)
            && entry.addr() as u64 <= start.as_u64()
            && (entry.addr() + entry.size()) as u64 >= end.as_u64()
    }) {
        panic!("heap is not backed by physical memory");
    }

    // Safety: The memory between 1MiB and 2MiB is not used for anything else, and
    // we have checked that this range is backed by physical memory.
    unsafe {
        crate::SHORT_TERM_ALLOC.lock().init(start.as_mut_ptr(), size);
    }
}

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;

    use super::*;

    #[test]
    fn simple_alloc() {
        let alloc = BumpAllocator::<16>::uninit();
        let val = Box::try_new_in([0u8; 16], &alloc);
        assert!(val.is_ok());
        let val = Box::try_new_in([0u8; 16], &alloc);
        assert!(val.is_err());
        let val = Box::try_new_in(0u8, &alloc);
        assert!(val.is_err());
    }

    #[test]
    fn two_alloc() {
        let alloc = BumpAllocator::<16>::uninit();
        let val = Box::try_new_in([0u8; 8], &alloc);
        assert!(val.is_ok());
        let val = Box::try_new_in([0u8; 8], &alloc);
        assert!(val.is_ok());
    }

    #[test]
    fn aligned_alloc() {
        #[repr(align(8))]
        struct Foo {
            x: u64,
            _y: u64,
        }
        // Allow for max 7-byte alignment + 2*8 (size of Foo)
        // The padding we need to use is ~random; it depends where exactly in memory our
        // buffer lands, as that is not required to be perfectly aligned with
        // any particular boundary.
        let alloc = BumpAllocator::<23>::uninit();
        let val = Box::new_in(Foo { x: 16, _y: 16 }, &alloc);
        assert_eq!(0, val.as_ref() as *const Foo as usize % core::mem::align_of::<Foo>());
        assert_eq!(16, val.x);
        // Even if the initial alignment was perfect by chance, we've used up 16 bytes,
        // so this won't fit
        let val = Box::try_new_in(Foo { x: 1, _y: 1 }, &alloc);
        assert!(val.is_err());
    }

    #[test]
    fn failing_alloc() {
        let alloc = BumpAllocator::<4>::uninit();
        assert!(Box::try_new_in(0u64, &alloc).is_err());
        assert!(Box::try_new_in(0u32, &alloc).is_ok());
        assert!(Box::try_new_in(0u8, &alloc).is_err());
    }
}
