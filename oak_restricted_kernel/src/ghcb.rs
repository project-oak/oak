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

use crate::mm::{ENCRYPTED_BIT_POSITION, KERNEL_OFFSET};
use sev_guest::{
    ghcb::{Ghcb, GhcbProtocol},
    msr::{
        change_snp_page_state, register_ghcb_location, PageAssignment, RegisterGhcbGpaRequest,
        SnpPageStateChangeRequest,
    },
    Translator,
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

/// The mask for the encrypted bit
const ENCRYPTED_BIT: u64 = 1 << ENCRYPTED_BIT_POSITION;

/// A wrapper to ensure that the GHCB is alone in alone in a 2MiB page.
///
/// We use 2MiB pages during early boot, so we must make sure there are no other kernel data
/// structures located in the page so that we can safely share the page with the hypervisor without
/// leaking other data.
#[derive(Debug)]
#[repr(C, align(2097152))]
struct GhcbAlignmentWrapper {
    ghcb: Ghcb,
}

static_assertions::assert_eq_size!(GhcbAlignmentWrapper, [u8; Size2MiB::SIZE as usize]);

static mut GHCB_WRAPPER: GhcbAlignmentWrapper = GhcbAlignmentWrapper { ghcb: Ghcb::new() };

/// Initializes the GHCB and shares it with the hypervisor during early boot.
pub fn init_ghcb_early(snp_enabled: bool) -> GhcbProtocol<'static, Ghcb> {
    // Safety: This is called only during early boot, so there is only a single execution context.
    let ghcb = unsafe { &mut GHCB_WRAPPER.ghcb };
    let translate = |vaddr: VirtAddr| {
        let address = vaddr.as_u64();
        // We assume a fixed offset mapping for kernel pages.
        if address < KERNEL_OFFSET {
            None
        } else {
            Some(PhysAddr::new(address - KERNEL_OFFSET))
        }
    };
    share_ghcb_with_hypervisor(ghcb, snp_enabled, translate);
    ghcb.reset();

    GhcbProtocol::new(ghcb, translate)
}

/// Marks the page containing the GHCB data structure to be shared with the hypervisor.
fn share_ghcb_with_hypervisor<VP: Translator>(ghcb: &Ghcb, snp_enabled: bool, translate: VP) {
    let ghcb_address = VirtAddr::new(ghcb as *const Ghcb as usize as u64);
    // On SEV-SNP we need to additionally update the RMP and register the GHCB location with the
    // hypervisor. We assume an identity mapping between virtual and physical addresses for now.
    if snp_enabled {
        // It is OK to crash if we cannot find a valid physica address for the GHCB.
        let ghcb_physical_address = translate(ghcb_address).unwrap();
        mark_2mib_page_shared_in_rmp(ghcb_physical_address);
        let ghcb_location_request =
            RegisterGhcbGpaRequest::new(ghcb_physical_address.as_u64() as usize)
                .expect("Invalid address for GHCB location");
        register_ghcb_location(ghcb_location_request)
            .expect("Couldn't register the GHCB address with the hypervisor");
    }
    // Mark the page as not encrypted in the page tables.
    set_encrypted_bit_for_page(&ghcb_address, false);
}

/// Sets the encrypted bit for the page that contains the address.
///
/// Since this is called during early boot, before the frame allocator of page mapper is initialised
/// we have to manually traverse the existing page tables. We use only 2MiB huge pages during early
/// boot.
fn set_encrypted_bit_for_page(address: &VirtAddr, encrypted: bool) {
    // Find the level 4 page table that is currently in use.
    let (l4_frame, _) = Cr3::read();
    // Safety: this is safe because we use the address of the current page table as configured in
    // the CR3 register.
    let l4_table = unsafe { get_mut_page_table_ref(physical_to_virtual(l4_frame.start_address())) };
    let l4_entry = &l4_table[address.p4_index()];
    // Make sure the entry pointing to the L3 page table is present.
    assert!(l4_entry.flags().contains(PageTableFlags::PRESENT));
    let l3_table_address = l4_entry.addr();
    assert!(l3_table_address.as_u64() > 0);
    // Safety: this is safe because we checked that the page table entry is marked as present and
    // the physical address is non-zero.
    let l3_table = unsafe { get_mut_page_table_ref(physical_to_virtual(l3_table_address)) };

    let l3_entry = &l3_table[address.p3_index()];
    // Make sure the entry pointing to the L2 page table is present.
    assert!(l3_entry.flags().contains(PageTableFlags::PRESENT));
    // Make sure it is not marked as a 1GiB huge page, so it points to an L2 page table.
    assert!(!l3_entry.flags().contains(PageTableFlags::HUGE_PAGE));
    let l2_table_address = l3_entry.addr();
    assert!(l2_table_address.as_u64() > 0);
    // Safety: this is safe because we checked that the page table entry is marked as present, not a
    // 1GiB huge page and the physical address is non-zero.
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

    // Flush the entire TLB to make sure the old value of the encrypted bit is not cached.
    flush_all();
}

/// Converts a physical address to a virtual address.
///
/// This must only be used during early boot when the page tables are still located in an identity
/// mapped region.
///
/// # Safety
///
/// This function requires that the page tables are in an identity mapped region of memory, which is
/// only the case during early boot before the kernel's memory initialisation.
unsafe fn physical_to_virtual(physical: PhysAddr) -> VirtAddr {
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
/// Panics if the physical address is not the start of a 2MiB page or if the page sharing request
/// fails.
fn mark_2mib_page_shared_in_rmp(physical_address: PhysAddr) {
    let raw_address = physical_address.as_u64();
    assert_eq!(align_down(raw_address, Size2MiB::SIZE), raw_address);
    // Since we don't have the GHCB set up already we need to use the MSR protocol to mark every
    // individual 4KiB area in the 2MiB page as shared.
    for i in 0..512 {
        let request = SnpPageStateChangeRequest::new(
            (raw_address + i * Size4KiB::SIZE) as usize,
            PageAssignment::Shared,
        )
        .expect("Invalid page address");
        change_snp_page_state(request).expect("Couldn't change page state");
    }
}
