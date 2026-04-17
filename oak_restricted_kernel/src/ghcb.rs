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

use core::ptr::addr_of;

use oak_core::sync::OnceCell;
use oak_sev_guest::{
    ghcb::{Ghcb, GhcbProtocol},
    io::{GhcbIoFactory, PortFactoryWrapper},
    msr::{
        PageAssignment, RegisterGhcbGpaRequest, change_snp_state_for_frame, register_ghcb_location,
    },
};
use spinning_top::Spinlock;
use x86_64::{
    addr::VirtAddr,
    registers::control::Cr3,
    structures::paging::{
        MappedPageTable, Page, PageSize, PhysFrame, Size2MiB, Size4KiB,
        mapper::PageTableFrameMapping,
    },
};

use crate::mm::{
    ENCRYPTED_BIT_POSITION, Mapper, PageTableFlags, Translator,
    encrypted_mapper::{EncryptedPageTable, MemoryEncryption, PhysOffset},
};

/// A wrapper to ensure that the GHCB is alone in a 2MiB page.
///
/// We use 2MiB pages during early boot, so we must make sure there are no other
/// kernel data structures located in the page so that we can safely share the
/// page with the hypervisor without leaking other data.
#[derive(Debug)]
#[repr(C, align(2097152))]
struct GhcbAlignmentWrapper {
    ghcb: Ghcb,
}

static_assertions::assert_eq_size!(GhcbAlignmentWrapper, [u8; Size2MiB::SIZE as usize]);

static mut GHCB_WRAPPER: GhcbAlignmentWrapper = GhcbAlignmentWrapper { ghcb: Ghcb::new() };

pub fn get_ghcb_port_factory() -> PortFactoryWrapper {
    PortFactoryWrapper::Ghcb(GhcbIoFactory::new(GHCB_PROTOCOL.get().expect("GHCB not initialized")))
}

pub static GHCB_PROTOCOL: OnceCell<Spinlock<GhcbProtocol<'static, Ghcb>>> = OnceCell::new();

/// Initializes the GHCB.
///
/// Will panic if the GHCB has already been initalized.
pub fn init(snp_enabled: bool) {
    let ghcb_protocol = init_ghcb_early(snp_enabled);
    if GHCB_PROTOCOL.set(Spinlock::new(ghcb_protocol)).is_err() {
        panic!("ghcb already initialized");
    }
}

/// Shares the page containing the GHCB with the hypervisor again.
///
/// This should be called as soon as the kernel memory has been initialised, as
/// that would have caused the page to be marked as encrypted.
pub fn reshare_ghcb<M: Mapper<Size4KiB>>(mapper: &M) {
    let ghcb_page = get_ghcb_page();
    // Safety: we only change the encrypted flag, all other flags for the GHCB pages
    // are as they were set during the kernel memory initialisation.
    unsafe {
        match mapper.update_flags(
            // Turn the 2M page into a 4K page. This unwrap will not fail, as 2M pages are
            // 4K-aligned by definition.
            Page::from_start_address(ghcb_page.start_address()).unwrap(),
            PageTableFlags::PRESENT
                | PageTableFlags::WRITABLE
                | PageTableFlags::GLOBAL
                | PageTableFlags::NO_EXECUTE,
        ) {
            Ok(mapper_flush) => mapper_flush.flush(),
            Err(error) => panic!("couldn't update page table flags for GHCB: {:?}", error),
        };
    }

    // Reset the GHCB in case something touched it while it was marked as encrypted.
    GHCB_PROTOCOL.get().expect("GHCB not initialized").lock().reset();
}

/// Initializes the GHCB and shares it with the hypervisor during early boot.
fn init_ghcb_early(snp_enabled: bool) -> GhcbProtocol<'static, Ghcb> {
    // Safety: This is called only during early boot, so there is only a single
    // execution context.
    #[allow(static_mut_refs)]
    let ghcb = unsafe { &mut GHCB_WRAPPER.ghcb };

    let ghcb_page = get_ghcb_page();
    let mapper = get_identity_mapped_encrypted_page_table();
    // Safety: we only remove the encrypted bit as the initial pages created by the
    // stage 0 firmware are only marked as present and writable, and possibly
    // encrypted.
    unsafe {
        match mapper.update_flags(ghcb_page, PageTableFlags::PRESENT | PageTableFlags::WRITABLE) {
            Ok(mapper_flush) => mapper_flush.flush(),
            Err(error) => panic!("couldn't update page table flags for GHCB: {:?}", error),
        };
    }
    if snp_enabled {
        // It is OK to crash if we cannot find the physical frame that contains the
        // GHCB.
        let ghcb_frame = PhysFrame::<Size2MiB>::from_start_address(
            mapper
                .translate_virtual(ghcb_page.start_address())
                .expect("couldn't find the physical address for the GHCB"),
        )
        .expect("the GHCB physical address is not correctly aligned");

        // Since we don't have the GHCB set up already we need to use the MSR protocol
        // to mark every individual 4KiB area in the 2MiB page as shared in the
        // RMP. It is OK to crash if we cannot share the GHCB with the
        // hypervisor.
        change_snp_state_for_frame(&ghcb_frame, PageAssignment::Shared)
            .expect("couldn't change SNP state for frame");

        let ghcb_location_request =
            RegisterGhcbGpaRequest::new(ghcb_frame.start_address().as_u64() as usize)
                .expect("invalid address for GHCB location");
        register_ghcb_location(ghcb_location_request)
            .expect("couldn't register the GHCB address with the hypervisor");
    }

    ghcb.reset();

    GhcbProtocol::new(ghcb, |virt_addr: VirtAddr| mapper.translate_virtual(virt_addr))
}

/// Gets a mapper that understands encrypted pages and assumes an identity
/// mapping.
///
/// This must only be used during early boot when the identity-mapped page
/// tables created by the stage 0 firmware is still active, and only if SEV,
/// SEV-ES or SEV-SNP is active.
fn get_identity_mapped_encrypted_page_table<'a>()
-> EncryptedPageTable<MappedPageTable<'a, PhysOffset>> {
    // We assume an identity mapping, so the offset is zero.
    let offset = VirtAddr::new(0);
    // We assume that this will only be used if memory encryption is enabled.
    let encryption = MemoryEncryption::Encrypted(ENCRYPTED_BIT_POSITION);
    let offset_mapper = PhysOffset::new(offset, encryption);
    // Find the level 4 page table that is currently in use.
    let (l4_frame, _) = Cr3::read();
    // Safety: we have fetched the address of the currently used PML4 table from
    // CR3, so this is a valid address pointing to a valid page table.
    let pml4 = unsafe { &mut *offset_mapper.frame_to_pointer(l4_frame) };
    EncryptedPageTable::new(pml4, offset, encryption)
}

/// Gets the 2MiB memory page that contains the GHCB.
fn get_ghcb_page() -> Page<Size2MiB> {
    // Safety: the reference to a mutable static is safe, as we only use it to
    // calculate a virtual address and don't dereference it.
    let ghcb_pointer = addr_of!(GHCB_WRAPPER);
    let ghcb_address = VirtAddr::from_ptr(ghcb_pointer);
    Page::<Size2MiB>::from_start_address(ghcb_address).expect("invalid start address for GHCB page")
}
