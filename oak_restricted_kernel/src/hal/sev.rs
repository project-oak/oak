//
// Copyright 2026 The Project Oak Authors
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

use core::arch::x86_64::CpuidResult;

pub mod mmio;
pub use mmio::SevMmio;
use oak_core::sync::OnceCell;
use oak_hal::{PageAssignment, PageEncryption, PortFactory};
use oak_sev_guest::msr::{SevStatus, get_sev_status};
use x86_64::structures::{
    paging::{Page, PhysFrame, Size4KiB},
    port::{PortRead, PortWrite},
};

use crate::{
    PAGE_TABLES,
    mm::Translator,
    snp::{get_snp_page_addresses, init_snp_pages},
};

static SEV_STATUS: OnceCell<SevStatus> = OnceCell::new();

fn sev_status() -> SevStatus {
    *SEV_STATUS.get().expect("SEV status not set")
}

pub struct Sev {}

impl crate::Platform for Sev {
    type Mmio = SevMmio;

    fn cpuid(_leaf: u32) -> CpuidResult {
        todo!();
    }

    /// # Safety
    ///
    /// The caller must ensure that the base address and the size represents a
    /// valid MMIO region.
    unsafe fn mmio(base_address: x86_64::PhysAddr, size: usize) -> Self::Mmio {
        let base_virt = PAGE_TABLES.lock().get().unwrap().translate_physical(base_address).unwrap();
        let use_ghcb = crate::ghcb::GHCB_PROTOCOL.get().is_some();

        // Safety: The caller must ensure that the physical MMIO base address and size
        // are valid. We translated the caller-provided base address to a valid
        // virtual address using the current valid page tables.
        unsafe { SevMmio::new(base_virt, base_address, size, use_ghcb) }
    }

    fn port_factory() -> PortFactory {
        if crate::ghcb::GHCB_PROTOCOL.get().is_some() {
            PortFactory {
                read_u8: |port| crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_read_u8(port),
                read_u16: |port| crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_read_u16(port),
                read_u32: |port| crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_read_u32(port),
                write_u8: |port, value| {
                    crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_write_u8(port, value)
                },
                write_u16: |port, value| {
                    crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_write_u16(port, value)
                },
                write_u32: |port, value| {
                    crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_write_u32(port, value)
                },
            }
        } else {
            // Fall back to direct port-based I/O when not running under
            // SEV-ES or SEV-SNP.
            PortFactory {
                read_u8: |port| unsafe { Ok(u8::read_from_port(port)) },
                read_u16: |port| unsafe { Ok(u16::read_from_port(port)) },
                read_u32: |port| unsafe { Ok(u32::read_from_port(port)) },
                write_u8: |port, value| {
                    unsafe { u8::write_to_port(port, value) };
                    Ok(())
                },
                write_u16: |port, value| {
                    unsafe { u16::write_to_port(port, value) };
                    Ok(())
                },
                write_u32: |port, value| {
                    unsafe { u32::write_to_port(port, value) };
                    Ok(())
                },
            }
        }
    }

    fn early_initialize_platform() {
        SEV_STATUS
            .set(get_sev_status().unwrap_or(SevStatus::empty()))
            .expect("SEV status already set");
        if sev_status().contains(SevStatus::SEV_ES_ENABLED) {
            crate::ghcb::init(sev_status().contains(SevStatus::SNP_ACTIVE));
        }
    }

    fn change_frame_state(frame: PhysFrame<Size4KiB>, state: PageAssignment) {
        if sev_status().contains(SevStatus::SNP_ACTIVE) {
            let page_gpa = frame.start_address().as_u64() as usize;

            let assignment = match state {
                PageAssignment::Shared => oak_sev_guest::msr::PageAssignment::Shared,
                PageAssignment::Private => oak_sev_guest::msr::PageAssignment::Private,
            };

            let request = oak_sev_guest::msr::SnpPageStateChangeRequest::new(page_gpa, assignment)
                .expect("failed to create SNP page state change request");

            oak_sev_guest::msr::change_snp_page_state(request)
                .expect("failed to change SNP page state");
        }
    }

    fn revalidate_page(_page: Page<Size4KiB>) {
        todo!();
    }

    fn page_table_mask(_encryption_state: PageEncryption) -> u64 {
        todo!();
    }

    fn encrypted() -> u64 {
        todo!();
    }

    fn wbvind() {
        todo!();
    }
}

impl oak_hal::MsrAccess for Sev {
    unsafe fn read_msr(_msr: u32) -> u64 {
        todo!();
    }

    unsafe fn write_msr(_msr: u32, _value: u64) {
        todo!();
    }
}

impl crate::hal::KernelPlatform for Sev {
    fn initialize_platform(info: &oak_linux_boot_params::BootParams) {
        let sev_status = sev_status();
        if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
            let pt_guard = PAGE_TABLES.lock();
            let mapper = pt_guard.get().unwrap();
            // Now that the page tables have been updated, we have to re-share the GHCB with
            // the hypervisor.
            crate::ghcb::reshare_ghcb(mapper);
            if sev_status.contains(SevStatus::SNP_ACTIVE) {
                // We must also initialise the CPUID and secrets pages and the guest message
                // encryptor when SEV-SNP is active. Panicking is OK at this point,
                // because these pages are required to support the full features and
                // we don't want to run without them.
                init_snp_pages(get_snp_page_addresses(info, mapper), mapper);
            }
        }
    }
}
