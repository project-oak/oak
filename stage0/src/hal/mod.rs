//
// Copyright 2024 The Project Oak Authors
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

pub mod base;

pub use base::Base;
#[cfg(test)]
use mockall;
use oak_attestation_types::{
    attester::Attester, transparent_attester::TransparentAttester, util::Serializable,
};
use oak_dice::evidence::TeePlatform;
pub use oak_hal::{Mmio, PageAssignment};
use oak_stage0_dice::DerivedKey;
use zerocopy::{FromBytes, IntoBytes};

use crate::{acpi::tables::Rsdp, zero_page::ZeroPage};

#[cfg(test)]
pub mod test_mocks {
    use core::arch::x86_64::CpuidResult;

    use oak_hal::{MsrAccess, PageAssignment, PortFactory};
    use oak_linux_boot_params::BootE820Entry;
    use x86_64::{
        PhysAddr,
        structures::paging::{Page, PageSize, Size4KiB},
    };

    use super::*;
    use crate::paging::PageEncryption;

    mockall::mock! {
        pub Platform {}
        impl oak_hal::Platform for Platform {
            type Mmio<S: PageSize> = <super::Base as oak_hal::Platform>::Mmio<S>;
            fn cpuid(leaf: u32) -> CpuidResult;
            unsafe fn mmio<S: PageSize + 'static>(base_address: PhysAddr) -> <Self as oak_hal::Platform>::Mmio<S>;
            fn port_factory() -> PortFactory;
            fn early_initialize_platform();
            fn initialize_platform(e820_table: &[BootE820Entry]);
            fn change_page_state(page: Page<Size4KiB>, state: PageAssignment);
            fn revalidate_page(page: Page<Size4KiB>);
            fn page_table_mask(encryption_state: PageEncryption) -> u64;
            fn encrypted() -> u64;
            fn wbvind();
            fn guest_phys_addr_size() -> u8;
        }
    }
    impl MsrAccess for MockPlatform {
        unsafe fn read_msr(_msr: u32) -> u64 {
            0
        }
        unsafe fn write_msr(_msr: u32, _value: u64) {}
    }
}
pub use oak_hal::Platform;
#[cfg(test)]
pub use test_mocks::MockPlatform;

#[cfg_attr(test, mockall::automock(
    type Attester = <Base as FirmwarePlatform>::Attester;
))]
pub trait FirmwarePlatform {
    type Attester: Attester + TransparentAttester + Serializable;

    /// Prefill E820 Table using platform specific features.
    ///
    /// Intel TDX requires the virtual firmware to consume inputs from TD HoB
    /// and measure them. This gets executed before asking the fw_cfg device
    /// for E820 table. It should populate the inner E820 table. If this
    /// function returns Ok, stage0 will not ask fw_cfg for E820 table.
    fn prefill_e820_table<T: IntoBytes + FromBytes + 'static>(
        input: &mut T,
    ) -> Result<usize, &'static str>;

    /// Platform-specific modifications and validations of ACPI tables, starting
    /// from RSDP, including RSDT, XSDT, APIC aka MADT.
    fn finalize_acpi_tables(rsdp: &mut Rsdp) -> Result<(), &'static str>;

    /// Platform-specific cleanups just before stage0 jumps to the kernel.
    ///
    /// The assumption is that after this operation there will no longer be any
    /// memory allocations or uses of the logging interface.
    fn deinit_platform();

    /// Populates platform-specific information in the zero page.
    ///
    /// Example: locations of the SEV Secrets and CPUID pages.
    fn populate_zero_page(zero_page: &mut ZeroPage);

    /// Returns an attester that can be used to extend the attestation
    /// information with an event log entry and serialize the attestation data
    /// so that it can be passed to the next boot stage.
    fn get_attester() -> Result<Self::Attester, &'static str>;

    /// Requests a derived key.
    ///
    /// The key is derived from the VCEK. The key derivation mixes in the VM
    /// launch measurement and guest policy and uses VMPL0.
    ///
    /// We use this key as the unique device secret for deriving compound
    /// devices identifiers for each layer, and eventually a sealing key in
    /// the last layer.
    fn get_derived_key() -> Result<DerivedKey, &'static str>;

    fn tee_platform() -> TeePlatform;
}

pub use oak_hal::{Msr, Port, PortFactory};
