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

use crate::mm::{
    encrypted_mapper::{EncryptedPageTable, MemoryEncryption, PhysOffset},
    Mapper, PageTableFlags, ENCRYPTED_BIT_POSITION, KERNEL_OFFSET,
};
use sev_guest::{
    ghcb::{Ghcb, GhcbProtocol},
    io::{GhcbIoFactory, PortFactoryWrapper},
    msr::{
        change_snp_page_state, get_sev_status, register_ghcb_location, PageAssignment,
        RegisterGhcbGpaRequest, SevStatus, SnpPageStateChangeRequest,
    },
    Translator,
};
use spinning_top::Spinlock;
use x86_64::{
    addr::{PhysAddr, VirtAddr},
    align_down,
    registers::control::Cr3,
    structures::paging::{
        page_table::PageTable, MappedPageTable, Page, PageSize, Size2MiB, Size4KiB,
    },
};

/// The mask for the encrypted bit.
const ENCRYPTED_BIT: u64 = 1 << ENCRYPTED_BIT_POSITION;

/// A wrapper to ensure that the GHCB is alone in a 2MiB page.
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

pub fn get_ghcb_port_factory() -> PortFactoryWrapper {
    PortFactoryWrapper::Ghcb(GhcbIoFactory::new(&GHCB_PROTOCOL))
}

// TODO(#3403): Stop initializing lazily once we have an equivalent to `std::sync::OnceLock`.
lazy_static! {
    static ref GHCB_PROTOCOL: Spinlock<GhcbProtocol<'static, Ghcb>> = {
        let sev_status = get_sev_status().unwrap_or(SevStatus::empty());
        Spinlock::new(init_ghcb_early(sev_status.contains(SevStatus::SNP_ACTIVE)))
    };
}

/// Shares the page containing the GHCB with the hypervisor again.
///
/// This should be called as soon as the kernel memory has been initialised, as that would have
/// caused the page to be marked as encrypted.
pub fn reshare_ghcb<M: Mapper<Size2MiB>>(mapper: &mut M) {
    // Safety: we only use the reference to calculate the address and never dereference it.
    let ghcb_address =
        unsafe { VirtAddr::new(&GHCB_WRAPPER as *const GhcbAlignmentWrapper as usize as u64) };
    // Panicking is OK if we cannot find a valid 2MiB page starting with the GHCB wrapper, or cannot
    // update the page table flags for it..
    let page = Page::<Size2MiB>::from_start_address(ghcb_address)
        .expect("Invalid start address for GHCB page.");

    // Safety: we dont change the address of the page or any of the existing flags, except for
    // removing the encrypted flag.
    unsafe {
        mapper
            .update_flags(
                page,
                OakPageTableFlags::PRESENT
                    | OakPageTableFlags::WRITABLE
                    | OakPageTableFlags::GLOBAL
                    | OakPageTableFlags::NO_EXECUTE,
            )
            .expect("Couldn't update page table flags for GHCB.")
            .flush();
    }
}

/// Initializes the GHCB and shares it with the hypervisor during early boot.
fn init_ghcb_early(snp_enabled: bool) -> GhcbProtocol<'static, Ghcb> {
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
    let ghcb_address = VirtAddr::from_ptr(ghcb as *const Ghcb);
    // On SEV-SNP we need to additionally update the RMP and register the GHCB location with the
    // hypervisor.
    if snp_enabled {
        // It is OK to crash if we cannot find a valid physical address for the GHCB.
        let ghcb_physical_address = translate(ghcb_address).unwrap();
        mark_2mib_page_shared_in_rmp(ghcb_physical_address);
        let ghcb_location_request =
            RegisterGhcbGpaRequest::new(ghcb_physical_address.as_u64() as usize)
                .expect("Invalid address for GHCB location");
        register_ghcb_location(ghcb_location_request)
            .expect("Couldn't register the GHCB address with the hypervisor");
    }
    let mut mapper = get_identity_mapper();
    // Make sure the encrypted bit is not set in the page table.
    // Safety: we only remove the encrypted bit as the initial pages created by the stage 0 firmware
    // are only marked as present and writable, and possibly encrypted.
    unsafe {
        set_single_2mib_page_flags(
            ghcb_address,
            &mut mapper,
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
        );
    }
}

/// Gets a mapper that understands encrypted pages and assumes an identity mapping.
///
/// This must only be used during early boot when the identity-mapped page tables created by the
/// stage 0 firmware is still active.
fn get_identity_mapper<'a>() -> EncryptedPageTable<MappedPageTable<'a, PhysOffset>> {
    // Find the level 4 page table that is currently in use.
    let (l4_frame, _) = Cr3::read();
    // Safety: this is safe because we use the address of the current page table as configured in
    // the CR3 register.
    let l4_table: &mut PageTable =
        unsafe { &mut *physical_to_virtual(l4_frame.start_address()).as_mut_ptr() };
    // For an identity mapping the offset is 0;
    let offset = VirtAddr::new(0);
    let encryption = MemoryEncryption::Encrypted(ENCRYPTED_BIT_POSITION);
    EncryptedPageTable::new(l4_table, offset, encryption)
}

/// Sets the specified flags for the 2MiB page that starts at the provided address.
///
/// # Safety
///
/// The caller must make sure that the changed flags does not cause undefined behaviour, such as
/// marking code pages as not executable.
unsafe fn set_single_2mib_page_flags<M: Mapper<Size2MiB>>(
    address: VirtAddr,
    mapper: &mut M,
    flags: PageTableFlags,
) {
    // Panicking is OK if we cannot find a valid 2MiB page starting with the GHCB, or cannot update
    // the page table flags for it.
    let page = Page::<Size2MiB>::from_start_address(address)
        .expect("Invalid start address for GHCB page.");

    match mapper.update_flags(page, flags) {
        Ok(mapper_flush) => mapper_flush.flush(),
        Err(error) => panic!("Couldn't update page table flags for GHCB: {:?}", error),
    };
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
