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

use core::mem::MaybeUninit;
use oak_linux_boot_params::{BootParams, E820EntryType};
use sev_guest::{
    ghcb::Ghcb,
    instructions::{pvalidate, InstructionError, PageSize as SevPageSize, Validation},
    msr::{
        change_snp_page_state, register_ghcb_location, PageAssignment, RegisterGhcbGpaRequest,
        SnpPageStateChangeRequest,
    },
};
use x86_64::{
    align_down, align_up,
    instructions::tlb,
    registers::control::Cr3,
    structures::paging::{PageSize, PageTable, PageTableFlags, PhysFrame, Size2MiB, Size4KiB},
    PhysAddr,
};

#[link_section = ".boot.ghcb"]
static mut GHCB: MaybeUninit<Ghcb> = MaybeUninit::uninit();

fn get_pd(encrypted: u64) -> &'static mut PageTable {
    let (pml4_frame, _) = Cr3::read();
    let pml4 =
        unsafe { &*((pml4_frame.start_address().as_u64() & !encrypted) as *const PageTable) };
    let pdpt = unsafe { &*((pml4[0].addr().as_u64() & !encrypted) as *const PageTable) };
    unsafe { &mut *((pdpt[0].addr().as_u64() & !encrypted) as *mut PageTable) }
}

pub fn init_ghcb(snp: bool, encrypted: u64) -> &'static mut Ghcb {
    let ghcb_addr = unsafe { GHCB.as_ptr() } as u64;

    // Remove the ENCRYPTED bit from the entry that maps the GHCB.
    let pd = get_pd(encrypted);
    let pt = unsafe { &mut *((pd[0].addr().as_u64() & !encrypted) as *mut PageTable) };
    let idx = (ghcb_addr / Size4KiB::SIZE) as usize;
    pt[idx].set_addr(
        PhysAddr::new(ghcb_addr),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );
    tlb::flush_all();

    // SNP requires extra handling beyond just removing the encrypted bit.
    if snp {
        let request = SnpPageStateChangeRequest::new(ghcb_addr as usize, PageAssignment::Shared)
            .expect("Invalid address for GHCB location");
        change_snp_page_state(request).expect("Could not change SNP state for GHCB");

        let ghcb_location_request = RegisterGhcbGpaRequest::new(ghcb_addr as usize)
            .expect("Invalid address for GHCB location");
        register_ghcb_location(ghcb_location_request)
            .expect("Couldn't register the GHCB address with the hypervisor");
    }

    unsafe { GHCB.write(Ghcb::new()) }
}

pub fn deinit_ghcb(snp: bool, encrypted: u64) {
    let ghcb_addr = unsafe { GHCB.as_ptr() } as u64;

    if snp {
        let request = SnpPageStateChangeRequest::new(ghcb_addr as usize, PageAssignment::Private)
            .expect("Invalid address for GHCB location");
        change_snp_page_state(request).expect("Could not change SNP state for GHCB");
    }

    let pd = get_pd(encrypted);
    let pt = unsafe { &mut *((pd[0].addr().as_u64() & !encrypted) as *mut PageTable) };
    let idx = (ghcb_addr / Size4KiB::SIZE) as usize;
    pt[idx].set_addr(
        PhysAddr::new(ghcb_addr | encrypted),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );
    tlb::flush_all();
}

/// Calls `PVALIDATE` on all memory ranges specified in the E820 table with type `RAM`.
pub fn validate_memory(zero_page: &BootParams, encrypted: u64) {
    let mut page_table = PageTable::new();

    // Find a location for our (temporary) page table. The initial page tables map [0..2MiB), so it
    // should be safe to put our temporary mappings at [2..4MiB).
    let pd = get_pd(encrypted);
    if pd[1].flags().contains(PageTableFlags::PRESENT) {
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
