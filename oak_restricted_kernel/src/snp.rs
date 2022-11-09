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

use crate::mm::Translator;
use anyhow::Context;
use core::slice::from_raw_parts;
use oak_core::sync::OnceCell;
use oak_linux_boot_params::{BootParams, CCBlobSevInfo, CCSetupData, SetupDataType};
use sev_guest::{cpuid::CpuidPage, secrets::SecretsPage};
use x86_64::{
    structures::paging::{PageSize, Size2MiB, Size4KiB},
    PhysAddr, VirtAddr,
};
use zerocopy::FromBytes;

/// The exclusive upper limit of the address range where we expect the SNP-specific pages to reside.
///
/// We expect the boot paramteres and the CPUID and secrets pages to all be placed in the first 1MiB
/// of physical memory by the Stage 0 Firmware, so we can use this range to help with validation.
const MAX_ADDRESS: PhysAddr = PhysAddr::new_truncate(Size2MiB::SIZE / 2);

/// The SEV-SNP secrets page.
pub static SECRETS_PAGE: OnceCell<SecretsPage> = OnceCell::new();

/// The SEV-SNP CPUID page.
pub static CPUID_PAGE: OnceCell<CpuidPage> = OnceCell::new();

/// Wrapper for the guest-physical addresses of the secrets page and the CPUID page.
pub struct SnpPageAddresses {
    pub secrets_page_address: PhysAddr,
    pub cpuid_page_address: PhysAddr,
}

/// Tries to extract the guest-physical addresses of the SEV-SNP secrets page and CPUID page.
///
/// This function must only be used while the identity mapping is still in place, since the pointers
/// in the boot paramter page was constructed by the Stage 0 firmware with an identity mapping.
pub fn try_get_snp_page_addresses(info: &BootParams) -> anyhow::Result<SnpPageAddresses> {
    let base_address = VirtAddr::from_ptr(info as *const BootParams);
    // We assume an identity mapping from virtual to physical address.
    let phys = PhysAddr::new(base_address.as_u64());
    // Check that the physical address is page-aligned and in the expected range below 1MiB.
    check_page_under_max_address(phys).context("Invalid boot parameter page")?;
    // The setup data is stored in a null-terminated linked list, so we step through the list until
    // we find and entry with the right type or reach the end.
    let mut setup_data_ptr = info.hdr.setup_data;
    while !setup_data_ptr.is_null() {
        check_pointer_in_4kib_page(setup_data_ptr, base_address)?;
        // Safety: we have checked that the pointer is not null and at least points to memory
        // within the boot paramter page.
        let setup_data = unsafe { &*setup_data_ptr };
        let type_ = setup_data.type_;
        if type_ == SetupDataType::CCBlob {
            break;
        }
        setup_data_ptr = setup_data.next;
    }

    if setup_data_ptr.is_null() {
        anyhow::bail!("Couldn't find setup data of type CCBlob.");
    }

    // Safety: we have checked that the pointer is not null, at least points to memory within the
    // boot paramter page and has the appropriate value for the type field set.
    let cc_blob_address =
        unsafe { &*(setup_data_ptr as *const CCSetupData) }.cc_blob_address as *const CCBlobSevInfo;

    check_pointer_in_4kib_page(cc_blob_address, base_address)?;
    // Safety: we have checked that the pointer is not null and at least points to memory within the
    // boot paramter page. We also validate the magic number as an additional check.
    let cc_blob = unsafe { &*cc_blob_address };
    let magic = cc_blob.magic;
    if magic != oak_linux_boot_params::CC_BLOB_SEV_INFO_MAGIC {
        anyhow::bail!("CCBlobSevInfo data structure has invalid magic: {}", magic);
    }

    let cpuid_page_address = PhysAddr::try_new(cc_blob.cpuid_phys as u64)
        .map_err(|_| anyhow::anyhow!("Invalid CPUID page physical address."))?;
    let secrets_page_address = PhysAddr::try_new(cc_blob.secrets_phys as u64)
        .map_err(|_| anyhow::anyhow!("Invalid secrets page physical address."))?;
    Ok(SnpPageAddresses {
        secrets_page_address,
        cpuid_page_address,
    })
}

/// Iinitializes the references to the SEV-SNP CPUID and secrets pages.
///
/// This function will panic if it is called more than once or if page addresses outside of the
/// expected range are supplied.
///
/// Panicking throughout this functions is OK, because if any of these values are invalid it means
/// the environment was not set up correctly and we don't know how to recover from that.
pub fn init_snp_pages<T: Translator>(snp_pages: SnpPageAddresses, mapper: &T) {
    // First make sure the addresses look OK: they are not null, point to the start of a 4KiB page,
    // and within the expected area.
    if snp_pages.cpuid_page_address.is_null() {
        panic!("CPUID page address is null.")
    }
    check_page_under_max_address(snp_pages.cpuid_page_address)
        .expect("Invalid CPUID page address.");
    if snp_pages.secrets_page_address.is_null() {
        panic!("Secrets page address is null.")
    }
    check_page_under_max_address(snp_pages.secrets_page_address)
        .expect("Invalid secrets page address.");

    let cpuid_page_address = mapper
        .translate_physical(snp_pages.cpuid_page_address)
        .expect("Couldn't find a valid virtual address for the CPUID page.");
    // Safety: we have checked that the pointer is in the expected valid memory range, not null, and
    // 4KiB page-aligned.
    let cpuid_slice: &[u8] =
        unsafe { from_raw_parts(cpuid_page_address.as_ptr(), Size4KiB::SIZE as usize) };
    CPUID_PAGE
        .set(CpuidPage::read_from(cpuid_slice).expect("CPUID page byte slice was invalid."))
        .expect("Couldn't set CPUID page.");

    let secrets_page_address = mapper
        .translate_physical(snp_pages.secrets_page_address)
        .expect("Couldn't find a valid virtual address for the secrets page.");
    // Safety: we have checked that the pointer is in the expected valid memory range, not null, and
    // 4KiB page-aligned.
    let secrets_slice: &[u8] =
        unsafe { from_raw_parts(secrets_page_address.as_ptr(), Size4KiB::SIZE as usize) };
    SECRETS_PAGE
        .set(SecretsPage::read_from(secrets_slice).expect("Secrets page byte slice was invalid."))
        .expect("Couldn't set secrets page.");
}

/// Checks that the physical address is the start of a 4KiB page that is below the maximum expected
/// address.
fn check_page_under_max_address(page: PhysAddr) -> anyhow::Result<()> {
    if page.align_down(Size4KiB::SIZE) != page {
        anyhow::bail!(
            "The address {:#018x} is not the start of a 4KiB page.",
            page
        );
    }
    if page >= MAX_ADDRESS {
        anyhow::bail!(
            "Address {:#018x} is not below the expected maximum address {:#018x}",
            page,
            MAX_ADDRESS
        )
    }
    Ok(())
}

/// Checks that the pointer points to an address that falls in the 4KiB page starting at
/// `page_start`.
fn check_pointer_in_4kib_page<T>(pointer: *const T, page_start: VirtAddr) -> anyhow::Result<()> {
    let address = VirtAddr::from_ptr(pointer);
    if address < page_start || address >= page_start + Size4KiB::SIZE {
        anyhow::bail!(
            "Pointer {:#018x} is not in the 4KiB page starting at {:#018x}",
            address,
            page_start
        )
    }
    Ok(())
}
