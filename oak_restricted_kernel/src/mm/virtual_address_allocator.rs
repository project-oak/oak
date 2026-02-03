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

use x86_64::structures::paging::{Page, PageSize, page::PageRange};

/// Extremely simple virtual memory address allocator using the bump algorithm.
///
/// The main goal for this allocator is to provide pages for things like the
/// kernel heap and kernel stack(s). As these data structures should live for
/// the entire lifetime of the kernel, we don't implement deallocation.
///
/// This allocator only hands out pages; mapping the pages to frames, as
/// necessary, is for the caller.
pub struct VirtualAddressAllocator<S: PageSize> {
    range: PageRange<S>,
    cursor: Page<S>,
}

impl<S: PageSize> VirtualAddressAllocator<S> {
    pub const fn new(range: PageRange<S>) -> Self {
        Self { range, cursor: range.start }
    }

    pub fn allocate(&mut self, count: u64) -> Option<PageRange<S>> {
        if self.cursor + count >= self.range.end {
            None
        } else {
            let cur = self.cursor;
            self.cursor += count;
            Some(Page::range(cur, self.cursor))
        }
    }
}
