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
use core::result::Result;
use linked_list_allocator::LockedHeap;
use log::info;

#[cfg(not(test))]
#[global_allocator]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

#[cfg(test)]
static ALLOCATOR: LockedHeap = LockedHeap::empty();

/// Initializes the global allocator from the largest contiguous slice of available memory.
///
/// Pointers to addresses in the memory area (or references to data contained within the slice) must
/// be considered invalid after calling this function, as the allocator may overwrite the data at
/// any point.
///
/// We ensure that data up address specified by `.stack_start` in the linker script is untouched,
/// even if it falls within the largest slice of memory.
///
/// Case in point, boot metadata is often stored somewhere in the memory area, so calling this takes
/// ownership of the `boot:BootInfo`, as the data provided to us by the bootloader will get
/// clobbered after initializing the heap.
pub fn init_allocator<E: boot::E820Entry, B: boot::BootInfo<E>>(
    info: B,
) -> Result<(), &'static str> {
    let ram_min = rust_hypervisor_firmware_boot::ram_min();
    let text_start = rust_hypervisor_firmware_boot::text_start();
    let text_end = rust_hypervisor_firmware_boot::text_end();
    let stack_start = rust_hypervisor_firmware_boot::stack_start();

    info!("RAM_MIN: {}", ram_min);
    info!("TEXT_START: {}", text_start);
    info!("TEXT_END: {}", text_end);
    info!("STACK_START: {}", stack_start);

    // Find the largest slice of memory and use that for the heap.
    let largest = info
        .e820_table()
        .iter()
        .inspect(|e| {
            info!(
                "E820 entry: [{:#016x}..{:#016x}) ({}), type {}",
                e.addr(),
                e.addr() + e.size(),
                e.size(),
                e.entry_type()
            );
        })
        .filter(|e| e.entry_type() == boot::E820EntryType::RAM)
        .max_by_key(|e| e.size())
        .ok_or("No RAM available for heap")?;

    // Ensure we don't clash with existing structures.
    let mut addr = largest.addr();
    let mut size = largest.size();

    if addr < stack_start {
        size -= stack_start - addr;
        addr = stack_start;
    }

    info!("Using [{:#016x}..{:#016x}) for heap.", addr, addr + size);
    // This is safe as we know the memory is available based on the e820 map.
    unsafe {
        ALLOCATOR.lock().init(addr as *mut u8, size);
    }
    Ok(())
}
