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
    alloc::Layout,
    mem::MaybeUninit,
    ptr::{write, NonNull},
    sync::atomic::{AtomicUsize, Ordering},
};
use spinning_top::Spinlock;

struct Inner<const N: usize> {
    index: AtomicUsize,
    storage: MaybeUninit<[u8; N]>,
}

impl<const N: usize> Inner<N> {
    const fn new() -> Self {
        Self {
            index: AtomicUsize::new(0),
            storage: MaybeUninit::uninit(),
        }
    }
}

/// Basic bump allocator that never deallocates memory.
///
/// The algorithm is rather simple: we maintain an index into the buffer we hold, that marks the
/// high water mark (already allocated memory). Whenever a request for memory comes in, me move the
/// index forward by the padding necessary to maintain proper alighment for the structure plus the
/// size of the structure.
///
/// We do not support deallocation, and there is no optimizations to pack the allocations as
/// efficiently as possible.
///
/// For stage0 uses these limitations are not an issue because (a) we use the allocator to allocate
/// data structures we expect to outive stage0 and (b) we allocate only a small number of data
/// structures, so the padding overhead is minimal.
pub struct Allocator<const N: usize> {
    inner: Spinlock<Inner<N>>,
}

impl<const N: usize> Allocator<N> {
    pub const fn uninit() -> Self {
        Self {
            inner: Spinlock::new(Inner::new()),
        }
    }

    pub fn allocate(&self, layout: Layout) -> Option<NonNull<u8>> {
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
            return None;
        }

        inner
            .index
            .fetch_add(align + layout.size(), Ordering::SeqCst);

        // Safety: we've reserved memory from [offset, offset + align + size) so this will not
        // exceed the bounds of `self.storage` and is not aliased.
        NonNull::new(unsafe { storage_ptr.add(offset + align) })
    }

    pub fn leak<T>(&self, val: T) -> Option<&mut T> {
        let ptr = self.allocate(Layout::for_value(&val))?.cast().as_ptr();

        // Safety: we've successfully allocated enough memory that is of the correct size, therefore
        // writing `val` to it is safe. We also ensure that the pointer is properly initialized and
        // aligned, so dereferencing it as a reference is fine.
        unsafe {
            write(ptr, val);
            ptr.as_mut()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_alloc() {
        let alloc = Allocator::<16>::uninit();
        let val = alloc.leak([0u8; 16]);
        assert!(val.is_some());
        let val = alloc.leak([0u8; 16]);
        assert!(val.is_none());
        let val = alloc.leak(0u8);
        assert!(val.is_none());
    }

    #[test]
    fn two_alloc() {
        let alloc = Allocator::<16>::uninit();
        let val = alloc.leak([0u8; 8]);
        assert!(val.is_some());
        let val = alloc.leak([0u8; 8]);
        assert!(val.is_some());
    }

    #[test]
    fn aligned_alloc() {
        #[repr(align(8))]
        struct Foo {
            x: u64,
            _y: u64,
        }
        // Allow for max 7-byte alignment + 2*8 (size of Foo)
        // The padding we need to use is ~random; it depends where exactly in memory our buffer
        // lands, as that is not required to be perfectly aligned with any particular boundary.
        let alloc = Allocator::<23>::uninit();
        let val = alloc.leak(Foo { x: 16, _y: 16 }).unwrap();
        assert_eq!(0, val as *const Foo as usize % core::mem::align_of::<Foo>());
        assert_eq!(16, val.x);
        // Even if the initial alignment was perfect by chance, we've used up 16 bytes, so this
        // won't fit
        let val = alloc.leak(Foo { x: 1, _y: 1 });
        assert!(val.is_none());
    }

    #[test]
    fn failing_alloc() {
        let alloc = Allocator::<4>::uninit();
        assert!(alloc.leak(0u64).is_none());
        assert!(alloc.leak(0u32).is_some());
        assert!(alloc.leak(0u8).is_none());
    }
}
