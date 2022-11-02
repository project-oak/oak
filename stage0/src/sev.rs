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

use oak_linux_boot_params::{BootParams, E820EntryType};
use sev_guest::instructions::{pvalidate, InstructionError, PageSize as SevPageSize, Validation};
use x86_64::{
    align_down, align_up,
    instructions::tlb,
    registers::control::Cr3,
    structures::paging::{PageSize, PageTable, PageTableFlags, PhysFrame, Size2MiB, Size4KiB},
    PhysAddr,
};

/// Calls `PVALIDATE` on all memory ranges specified in the E820 table with type `RAM`.
pub fn validate_memory(zero_page: &BootParams, encrypted: u64) {
    let mut page_table = PageTable::new();

    // Find a location for our (temporary) page table. The initial page tables map [0..2MiB), so it
    // should be safe to put our temporary mappings at [2..4MiB).
    let (pml4_frame, _) = Cr3::read();
    let pml4 =
        unsafe { &*((pml4_frame.start_address().as_u64() & !encrypted) as *const PageTable) };
    let pdpt = unsafe { &*((pml4[0].addr().as_u64() & !encrypted) as *const PageTable) };
    let pd = unsafe { &mut *((pdpt[0].addr().as_u64() & !encrypted) as *mut PageTable) };
    if !pd[1].is_unused() {
        panic!("PD[1] is in use");
    }
    pd[1].set_addr(
        PhysAddr::new(&page_table as *const _ as u64 | encrypted),
        PageTableFlags::PRESENT,
    );

    for entry in zero_page.e820_table() {
        if entry.entry_type() != E820EntryType::RAM {
            continue;
        }

        let mut range = PhysFrame::<Size4KiB>::range(
            PhysFrame::from_start_address(PhysAddr::new(align_up(
                entry.addr() as u64,
                Size4KiB::SIZE,
            )))
            .unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(align_down(
                (entry.addr() + entry.size()) as u64,
                Size4KiB::SIZE,
            )))
            .unwrap(),
        );

        // Our temporary page table will only fit 512 4K frames at a time, so iterate in chunks of
        // 512 (with the last one being smaller if needed)
        while page_table
            .iter_mut()
            .map(|pte| {
                if let Some(frame) = range.next() {
                    pte.set_addr(frame.start_address() + encrypted, PageTableFlags::PRESENT);
                    1
                } else {
                    0
                }
            })
            .sum::<u64>()
            > 0
        {
            tlb::flush_all();

            if let Some(err) = page_table
                .iter()
                .enumerate()
                .filter(|(_, entry)| !entry.is_unused())
                .map(|(n, _)| {
                    pvalidate(
                        Size2MiB::SIZE as usize + (n * Size4KiB::SIZE as usize),
                        SevPageSize::Page4KiB,
                        Validation::Validated,
                    )
                })
                .map(|result| match result {
                    Err(InstructionError::ValidationStatusNotUpdated) => Ok(()),
                    other => other,
                })
                .find(|result| result.is_err())
            {
                panic!("Unexpected error: {:?}", err);
            }

            page_table.zero();
        }
    }
    pd[1].set_unused();
    tlb::flush_all();
}
