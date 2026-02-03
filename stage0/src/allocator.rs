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

use alloc::boxed::Box;
use core::{
    alloc::{AllocError, Allocator, Layout},
    marker::PhantomData,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use spinning_top::Spinlock;
use x86_64::{
    VirtAddr,
    structures::paging::{Page, PageSize, Size4KiB},
};

use crate::{
    Platform,
    paging::{share_page, unshare_page},
};

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
///
/// N is the capacity in bytes.
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
/// Allocator that forces allocations to be 4K-aligned (and sized) and marks the
/// pages as shared.
///
/// This allocator is inefficient as it will only allocate 4K chunks,
/// potentially wasting memory. For example, if you allocate two u32-s, although
/// they could well fit on one page, currently that'd use 8K of memory.
/// That, however, is an implementation detail, and may change in the future.
#[repr(transparent)]
struct SharedAllocator<A: Allocator, P: Platform> {
    inner: A,
    _phantom: PhantomData<P>,
}

impl<A: Allocator, P: Platform> SharedAllocator<A, P> {
    fn new(allocator: A) -> Self {
        Self { inner: allocator, _phantom: PhantomData }
    }
}

unsafe impl<A: Allocator, P: Platform> Allocator for SharedAllocator<A, P> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let layout =
            layout.align_to(Size4KiB::SIZE as usize).map_err(|_| AllocError)?.pad_to_align();
        let allocation = self.inner.allocate(layout)?;
        for offset in (0..allocation.len()).step_by(Size4KiB::SIZE as usize) {
            // Safety: the allocation has succeeded and the offset won't exceed the size of
            // the allocation.
            share_page::<P>(Page::containing_address(VirtAddr::from_ptr(unsafe {
                allocation.as_non_null_ptr().as_ptr().add(offset)
            })))
        }
        Ok(allocation)
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let layout = layout
            .align_to(Size4KiB::SIZE as usize)
            .map_err(|_| AllocError)
            .unwrap()
            .pad_to_align();
        for offset in (0..layout.size()).step_by(Size4KiB::SIZE as usize) {
            // Safety: the allocation has succeeded and the offset won't exceed the size of
            // the allocation.
            unshare_page::<P>(Page::containing_address(VirtAddr::from_ptr(unsafe {
                ptr.as_ptr().add(offset)
            })))
        }
        unsafe { self.inner.deallocate(ptr, layout) }
    }
}

/// Stores a data structure on a shared page.
pub struct Shared<T: 'static, A: Allocator, P: Platform> {
    inner: Box<T, SharedAllocator<A, P>>,
}

impl<T, A: Allocator, P: Platform> Shared<T, A, P> {
    pub fn new_in(t: T, alloc: A) -> Self
    where
        A: 'static,
    {
        Self { inner: Box::new_in(t, SharedAllocator::new(alloc)) }
    }

    /// See `Box::from_raw_in` for documentation.
    ///
    /// # Safety
    ///
    /// The caller needs to guarantee that (a) the pointer was obtained by
    /// `Shared::leak` and (b) the allocator you pass in is exactly the same as
    /// was used for the original allocation of the `Shared`.
    ///
    /// Again, see `Box::from_raw_in` for more details.
    pub unsafe fn from_raw_in(raw: *mut T, alloc: A) -> Shared<T, A, P> {
        Self { inner: unsafe { Box::from_raw_in(raw, SharedAllocator::new(alloc)) } }
    }

    /// See `Box::leak` for documentation.
    pub fn leak<'a>(s: Shared<T, A, P>) -> &'a mut T
    where
        A: 'a,
        P: 'a,
    {
        Box::leak(s.inner)
    }
}

impl<T, A: Allocator, P: Platform> Deref for Shared<T, A, P> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T, A: Allocator, P: Platform> DerefMut for Shared<T, A, P> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T, A: Allocator, P: Platform> AsRef<T> for Shared<T, A, P> {
    fn as_ref(&self) -> &T {
        &self.inner
    }
}

impl<T, A: Allocator, P: Platform> AsMut<T> for Shared<T, A, P> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.inner
    }
}

pub fn init_global_allocator(e820_table: &[BootE820Entry]) {
    // Create the heap after the Mailbox
    let start = VirtAddr::new(0x103000);
    // stage0 stays below 2MiB. The heap size is 1MiB - 3 pages
    let size = (0x10_0000 - 0x3000) as usize;
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
