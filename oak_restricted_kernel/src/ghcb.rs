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
    Mapper, PageTableFlags, Translator, ENCRYPTED_BIT_POSITION,
};
use lazy_static::lazy_static;
use sev_guest::{
    ghcb::{Ghcb, GhcbProtocol},
    io::{GhcbIoFactory, PortFactoryWrapper},
    msr::{
        change_snp_page_state, get_sev_status, register_ghcb_location, PageAssignment,
        RegisterGhcbGpaRequest, SevStatus, SnpPageStateChangeRequest,
    },
};
use spinning_top::Spinlock;
use x86_64::{
    addr::VirtAddr,
    registers::control::Cr3,
    structures::paging::{
        mapper::PageTableFrameMapping, MappedPageTable, Page, PageSize, PhysFrame, Size2MiB,
        Size4KiB,
    },
};

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
    let ghcb_page = get_ghcb_page();
    // Safety: we only change the encrypted flag, all other flags for the GHCB pages are as they
    // were set during the kernel memory initialisation.
    unsafe {
        match mapper.update_flags(
            ghcb_page,
            PageTableFlags::PRESENT
                | PageTableFlags::WRITABLE
                | PageTableFlags::GLOBAL
                | PageTableFlags::NO_EXECUTE,
        ) {
            Ok(mapper_flush) => mapper_flush.flush(),
            Err(error) => panic!("Couldn't update page table flags for GHCB: {:?}", error),
        };
    }
}

/// Initializes the GHCB and shares it with the hypervisor during early boot.
fn init_ghcb_early(snp_enabled: bool) -> GhcbProtocol<'static, Ghcb> {
    // Safety: This is called only during early boot, so there is only a single execution context.
    let ghcb = unsafe { &mut GHCB_WRAPPER.ghcb };
    ghcb.reset();

    let ghcb_page = get_ghcb_page();
    let mut mapper = get_identity_mapped_encrypted_page_table();
    if snp_enabled {
        // It is OK to crash if we cannot find the physical frame that contains the GHCB.
        let ghcb_frame = PhysFrame::<Size2MiB>::from_start_address(
            mapper
                .translate_virtual(ghcb_page.start_address())
                .expect("Couldn't find the physical address for the GHCB"),
        )
        .expect("The GHCB physical address is not correctly aligned");

        mark_frame_shared_in_rmp(&ghcb_frame);

        let ghcb_location_request =
            RegisterGhcbGpaRequest::new(ghcb_frame.start_address().as_u64() as usize)
                .expect("Invalid address for GHCB location");
        register_ghcb_location(ghcb_location_request)
            .expect("Couldn't register the GHCB address with the hypervisor");
    }

    // Safety: we only remove the encrypted bit as the initial pages created by the stage 0 firmware
    // are only marked as present and writable, and possibly encrypted.
    unsafe {
        match mapper.update_flags(
            ghcb_page,
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
        ) {
            Ok(mapper_flush) => mapper_flush.flush(),
            Err(error) => panic!("Couldn't update page table flags for GHCB: {:?}", error),
        };
    }

    GhcbProtocol::new(ghcb, |virt_addr: VirtAddr| {
        mapper.translate_virtual(virt_addr)
    })
}

/// Gets a mapper that understands encrypted pages and assumes an identity mapping.
///
/// This must only be used during early boot when the identity-mapped page tables created by the
/// stage 0 firmware is still active, and only if SEV, SEV-ES or SEV-SNP is active.
fn get_identity_mapped_encrypted_page_table<'a>(
) -> EncryptedPageTable<MappedPageTable<'a, PhysOffset>> {
    // We assume an identity mapping, so the offset is zero.
    let offset = VirtAddr::new(0);
    // We assume that this will only be used if memory encryption is enabled.
    let encryption = MemoryEncryption::Encrypted(ENCRYPTED_BIT_POSITION);
    let offset_mapper = PhysOffset::new(offset, encryption);
    // Find the level 4 page table that is currently in use.
    let (l4_frame, _) = Cr3::read();
    // Safety: we have fetched the address of the currently used PML4 table from CR3, so this is a
    // valid address pointing to a valid page table.
    let pml4 = unsafe { &mut *offset_mapper.frame_to_pointer(l4_frame) };
    EncryptedPageTable::new(pml4, offset, encryption)
}

/// Marks a 2MiB physical frame as shared in the SEV-SNP reverse-map table (RMP).
fn mark_frame_shared_in_rmp(frame: &PhysFrame<Size2MiB>) {
    let raw_address = frame.start_address().as_u64();
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

/// Gets the 2MiB memory page that contains the GHCB.
fn get_ghcb_page() -> Page<Size2MiB> {
    // Safety: the reference to a mutable static is safe, as we only use it to calculate a virtual
    // address and don't dereference it.
    let ghcb_pointer = unsafe { &GHCB_WRAPPER as *const GhcbAlignmentWrapper };
    let ghcb_address = VirtAddr::from_ptr(ghcb_pointer);
    Page::<Size2MiB>::from_start_address(ghcb_address)
        .expect("Invalid start address for GHCB page.")
}
