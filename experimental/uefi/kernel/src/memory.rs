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

use linked_list_allocator::LockedHeap;
use rust_hypervisor_firmware_subset::boot;

use log::info;

#[cfg(not(test))]
#[global_allocator]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

#[cfg(test)]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

pub fn init_allocator(info: &dyn boot::Info) {
    let ram_min = rust_hypervisor_firmware_subset::ram_min();
    let text_start = rust_hypervisor_firmware_subset::text_start();
    let text_end = rust_hypervisor_firmware_subset::text_end();
    let stack_start = rust_hypervisor_firmware_subset::stack_start();

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

    // Ensure we don't clash with existing structures.
    if entry.addr < stack_start {
        entry.size -= stack_start - entry.addr;
        entry.addr = stack_start;
    }

    info!("Using {:?} for heap.", entry);
    // This is safe as we know the memory is available based on the e820 map.
    unsafe {
        ALLOCATOR.lock().init(
            entry.addr.try_into().unwrap(),
            entry.size.try_into().unwrap(),
        );
    }
}
