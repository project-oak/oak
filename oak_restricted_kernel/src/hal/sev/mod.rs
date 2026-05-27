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
use oak_hal::{PageAssignment, PageEncryption, PortFactory};
use oak_linux_boot_params::BootE820Entry;
use x86_64::structures::paging::{Page, Size4KiB};

use crate::{PAGE_TABLES, mm::Translator};

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
        todo!();
    }

    fn early_initialize_platform() {
        todo!();
    }

    fn initialize_platform(_e820_table: &[BootE820Entry]) {
        todo!();
    }

    fn change_page_state(_page: Page<Size4KiB>, _state: PageAssignment) {
        todo!();
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
