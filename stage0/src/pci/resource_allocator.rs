//
// Copyright 2025 The Project Oak Authors
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

use core::ops::{Add, Range};

pub trait ResourceAllocatorIdx: Add<Output = Self> + PartialOrd + Sized + Clone + Copy {
    fn next_multiple_of(self, rhs: Self) -> Self;
}

impl ResourceAllocatorIdx for u16 {
    fn next_multiple_of(self, rhs: Self) -> Self {
        self.next_multiple_of(rhs)
    }
}

impl ResourceAllocatorIdx for u32 {
    fn next_multiple_of(self, rhs: Self) -> Self {
        self.next_multiple_of(rhs)
    }
}

impl ResourceAllocatorIdx for u64 {
    fn next_multiple_of(self, rhs: Self) -> Self {
        self.next_multiple_of(rhs)
    }
}

/// Generic allocator for arbitrary PCI resources.
///
/// This allocator deals with contiguous chunks of numeric resources (e.g.
/// memory ranges or I/O ports).
///
/// The current implementation has some limitations:
/// 1. No deallocation is supported, you can only allocate resources.
/// 2. The algorithm is a basic bump allocator, which means the allocations only
///    grow up. Alignment requirements may force chunks of resources to be
///    abandoned, even if some future allocation request would fit.
pub struct ResourceAllocator<Idx: ResourceAllocatorIdx> {
    range: Range<Idx>,
    index: Idx,
}

impl<Idx: ResourceAllocatorIdx> ResourceAllocator<Idx> {
    pub fn new(range: Range<Idx>) -> Self {
        let index = range.start;
        Self { range, index }
    }

    /// Allocate resources from this allocator.
    ///
    /// The returned Range is guaranteed to both:
    /// (a) be `size`-aligned, and
    /// (b) be `size` in size.
    ///
    /// If the request cannot be satisfied, returns `None`.
    pub fn allocate(&mut self, size: Idx) -> Option<Range<Idx>> {
        // Ensure alignment with `size`.
        let index = self.index.next_multiple_of(size);
        if index + size > self.range.end {
            None
        } else {
            let result = index..index + size;
            self.index = index + size;
            Some(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;

    use super::*;

    #[googletest::test]
    fn test_resource_allocator() {
        let mut allocator = ResourceAllocator::new(16u32..128u32);
        assert_that!(allocator.allocate(16), some(eq(&(16..32))));
        assert_that!(allocator.allocate(64), some(eq(&(64..128))));
        assert_that!(allocator.allocate(16), none());
    }
}
