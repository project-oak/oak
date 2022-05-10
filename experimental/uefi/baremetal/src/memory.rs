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

use crate::bootparam;
use linked_list_allocator::LockedHeap;

#[global_allocator]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

extern "C" {
    #[link_name = "stack_end"]
    static STACK_END: core::ffi::c_void;
}

pub fn stack_end() -> u64 {
    unsafe { &STACK_END as *const _ as u64 }
}

pub fn init_allocator(info: &bootparam::boot_params) {
    let stack_end = stack_end();
    // Find the largest slice of memory and use that for the heap.
    let mut largest: Option<bootparam::boot_e820_entry> = None;
    for i in 0..info.e820_entries {
        let entry = &info.e820_table[i as usize];
        // We have to extract these due to unaligned access
        let addr = entry.addr;
        let size = entry.size;
        let entry_type = entry.type_;
        info!(
            "E820 entry: [{:#016x} - {:#016x}] ({}), type {}",
            addr,
            addr + size,
            size,
            entry_type
        );

        if entry.type_ == 1 && largest.map_or(0, |e| e.size) < entry.size {
            largest = Some(*entry);
        }
    }

    // If we really have no memory at all, crash and burn.
    let mut entry = largest.unwrap();

    // Ensure we don't clash with existing structures.
    if entry.addr < stack_end {
        entry.size -= stack_end - entry.addr;
        entry.addr = stack_end;
    }

    let addr = entry.addr;
    let size = entry.size;
    info!("Using [{:#016x} - {:#016x}] for heap.", addr, addr + size);
    // This is safe as we know the memory is available based on the e820 map.
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
