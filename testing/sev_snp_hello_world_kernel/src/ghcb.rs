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

use oak_sev_guest::{
    ghcb::{Ghcb, GhcbProtocol},
    msr::{
        change_snp_page_state, register_ghcb_location, PageAssignment, RegisterGhcbGpaRequest,
        SnpPageStateChangeRequest,
    },
};
use x86_64::{
    addr::{PhysAddr, VirtAddr},
    align_down,
    instructions::tlb::flush_all,
    registers::control::Cr3,
    structures::paging::{
        page_table::{PageTable, PageTableFlags},
        PageSize, Size2MiB, Size4KiB,
    },
};

/// The mask for the encrypted bit. For now we assume that we will be running on
/// AMD Arcadia-Milan CPUs, which use bit 51.
const ENCRYPTED_BIT: u64 = 1 << 51;

#[link_section = ".ghcb"]
static mut GHCB: MaybeUninit<Ghcb> = MaybeUninit::uninit();

/// Initializes the GHCB and shares it with the hypervisor.
pub fn init_ghcb(snp_enabled: bool) -> GhcbProtocol<'static, Ghcb> {
    // Safety: this data structure is placed in valid memory so we won't page fault
    // when accessing it. We reset the value of the GHCB immediately after
    // shareing it with the hypervisor, so it will be fine if it is not
    // initialized.
    let ghcb: &mut Ghcb = unsafe { GHCB.assume_init_mut() };
    share_ghcb_with_hypervisor(ghcb, snp_enabled);
    ghcb.reset();
    // We are using an identity mapping between virtual and physical addresses.
    GhcbProtocol::new(ghcb, |vaddr: VirtAddr| Some(PhysAddr::new(vaddr.as_u64())))
}

/// Marks the page containing the GHCB data structure to be shared with the
/// hypervisor.
fn share_ghcb_with_hypervisor(ghcb: &Ghcb, snp_enabled: bool) {
    let ghcb_address = VirtAddr::new(ghcb as *const Ghcb as usize as u64);
    if snp_enabled {
        // On SEV-SNP we need to additionally update the RMP and register the GHCB
        // location with the hypervisor. We assume an identity mapping between
        // virtual and physical addresses for now.
        let ghcb_physical_address = PhysAddr::new(ghcb_address.as_u64());
        mark_2mib_page_shared_in_rmp(ghcb_physical_address);
        let ghcb_location_request =
            RegisterGhcbGpaRequest::new(ghcb_physical_address.as_u64() as usize)
                .expect("invalid address for GHCB location");
        register_ghcb_location(ghcb_location_request)
            .expect("couldn't register the GHCB address with the hypervisor");
    }
    // Mark the page as not encrypted in the page tables.
    set_encrypted_bit_for_page(&ghcb_address, false);
}

/// Sets the encrypted bit for the page that contains the address.
///
/// We assume for now that we will always use 2MiB huge pages.
fn set_encrypted_bit_for_page(address: &VirtAddr, encrypted: bool) {
    // Find the level 4 page table that is currently in use.
    let (l4_frame, _) = Cr3::read();
    // Safety: this is safe because we use the address of the current page table as
    // configured in the CR3 register.
    let l4_table = unsafe { get_mut_page_table_ref(physical_to_virtual(l4_frame.start_address())) };
    let l4_entry = &l4_table[address.p4_index()];
    // Make sure the entry pointing to the L3 page table is present.
    assert!(l4_entry.flags().contains(PageTableFlags::PRESENT));
    let l3_table_address = l4_entry.addr();
    assert!(l3_table_address.as_u64() > 0);
    // Safety: this is safe because we checked that the page table entry is marked
    // as present and the physical address is non-zero.
    let l3_table = unsafe { get_mut_page_table_ref(physical_to_virtual(l3_table_address)) };

    let l3_entry = &l3_table[address.p3_index()];
    // Make sure the entry pointing to the L2 page table is present.
    assert!(l3_entry.flags().contains(PageTableFlags::PRESENT));
    // Make sure it is not marked as a 1GiB huge page, so it points to an L2 page
    // table.
    assert!(!l3_entry.flags().contains(PageTableFlags::HUGE_PAGE));
    let l2_table_address = l3_entry.addr();
    assert!(l2_table_address.as_u64() > 0);
    // Safety: this is safe because we checked that the page table entry is marked
    // as present, not a 1GiB huge page and the physical address is non-zero.
    let l2_table = unsafe { get_mut_page_table_ref(physical_to_virtual(l2_table_address)) };

    let page_entry = &mut l2_table[address.p2_index()];
    let flags = page_entry.flags();
    let page_frame_address = page_entry.addr();
    // Make sure the entry for the L2 page table is present.
    assert!(flags.contains(PageTableFlags::PRESENT));
    // Make sure it is marked as a 2MiB huge page.
    assert!(flags.contains(PageTableFlags::HUGE_PAGE));

    let page_frame_address = PhysAddr::new(if encrypted {
        page_frame_address.as_u64() | ENCRYPTED_BIT
    } else {
        page_frame_address.as_u64() & !ENCRYPTED_BIT
    });

    page_entry.set_addr(page_frame_address, flags);

    // Flush the entire TLB to make sure the old value of the encrypted bit is not
    // cached.
    flush_all();
}

/// Converts a physical address to a virtual address.
///
/// This assumes an identity mapping and corrects for the encrypted bit in case
/// it is set.
fn physical_to_virtual(physical: PhysAddr) -> VirtAddr {
    let normalized = physical.as_u64() & !ENCRYPTED_BIT;
    VirtAddr::new(normalized)
}

/// Gets a mutable reference to a page table that starts at the given address.
///
/// # Safety
///
/// The caller must provide a valid address for the start of a valid page table.
unsafe fn get_mut_page_table_ref<'a>(start_address: VirtAddr) -> &'a mut PageTable {
    &mut *(start_address.as_u64() as usize as *mut PageTable)
}

/// Marks a 2MiB page as shared in the SEV-SNP reverse-map table (RMP).
///
/// Panics if the physical address is not the start of a 2MiB page or if the
/// page sharing request fails.
fn mark_2mib_page_shared_in_rmp(physical_address: PhysAddr) {
    let raw_address = physical_address.as_u64();
    assert_eq!(align_down(raw_address, Size2MiB::SIZE), raw_address);
    // Since we don't have the GHCB set up already we need to use the MSR protocol
    // to mark every individual 4KiB area in the 2MiB page as shared.
    for i in 0..512 {
        let request = SnpPageStateChangeRequest::new(
            (raw_address + i * Size4KiB::SIZE) as usize,
            PageAssignment::Shared,
        )
        .expect("invalid page address");
        change_snp_page_state(request).expect("couldn't change page state");
    }
}
