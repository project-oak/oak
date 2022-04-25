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
// Portions Copyright © 2019 Intel Corporation.

use crate::boot;
use core::ffi::c_void;
use linked_list_allocator::LockedHeap;

#[global_allocator]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

const PAGE_SIZE: u64 = 4096;

extern "C" {
    #[link_name = "ram_min"]
    static RAM_MIN: c_void;
    #[link_name = "text_start"]
    static TEXT_START: c_void;
    #[link_name = "text_end"]
    static TEXT_END: c_void;
    #[link_name = "stack_start"]
    static STACK_START: c_void;
}

pub fn init_allocator(info: &dyn boot::Info) {
    let ram_min = unsafe { &RAM_MIN as *const _ as u64 };
    let text_start = unsafe { &TEXT_START as *const _ as u64 };
    let text_end = unsafe { &TEXT_END as *const _ as u64 };
    let stack_start = unsafe { &STACK_START as *const _ as u64 };
    assert!(ram_min % PAGE_SIZE == 0);
    assert!(text_start % PAGE_SIZE == 0);
    assert!(text_end % PAGE_SIZE == 0);
    assert!(stack_start % PAGE_SIZE == 0);

    info!("RAM_MIN: {}", ram_min);
    info!("TEXT_START: {}", text_start);
    info!("TEXT_END: {}", text_end);
    info!("STACK_START: {}", stack_start);

    // Find the largest slice of memory and use that for the heap.
    let mut largest: Option<boot::E820Entry> = None;
    for i in 0..info.num_entries() {
        let entry = info.entry(i);
        // We have to extract these due to unaligned access
        let addr = entry.addr;
        let size = entry.size;
        let entry_type = entry.entry_type;
        info!(
            "E820 entry: [{:#016x} - {:#016x}] ({}), type {}",
            addr,
            addr + size,
            size,
            entry_type
        );
        if entry.entry_type == boot::E820Entry::RAM_TYPE
            && largest.map_or(0, |e| e.size) < entry.size
        {
            largest = Some(entry);
        }
    }

    // If we really have no memory at all, crash and burn.
    let mut entry = largest.unwrap();
    // Don't allocate over existing structures.
    if entry.addr < stack_start {
        entry.size -= stack_start - entry.addr;
        entry.addr = stack_start;
    }
    info!("Using {:?} for heap.", entry);
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
