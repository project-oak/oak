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

use crate::boot;
use linked_list_allocator::LockedHeap;

#[global_allocator]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

pub fn init_allocator(info: &dyn boot::Info) {
    // Find the largest slice of memory and use that for the heap.
    let mut largest: Option<boot::E820Entry> = None;
    for i in 0..info.num_entries() {
        let entry = info.entry(i);
        if entry.entry_type == boot::E820Entry::RAM_TYPE
            && largest.map_or(0, |e| e.size) < entry.size
        {
            largest = Some(entry);
        }
    }

    // If we really have no memory at all, crash and burn.
    let entry = largest.unwrap();
    unsafe {
        ALLOCATOR.lock().init(
            entry.addr.try_into().unwrap(),
            entry.size.try_into().unwrap(),
        );
    }
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("Error allocating memory: {:#?}", layout);
}
