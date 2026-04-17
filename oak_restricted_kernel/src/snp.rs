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

use core::{panic, slice::from_raw_parts};

use oak_core::sync::OnceCell;
use oak_linux_boot_params::{BootParams, CCBlobSevInfo, CCSetupData, SetupDataType};
use oak_sev_guest::{cpuid::CpuidPage, secrets::SecretsPage};
use x86_64::{
    PhysAddr, VirtAddr,
    structures::paging::{PageSize, Size4KiB},
};
use zerocopy::FromBytes;

use crate::mm::Translator;

/// The exclusive upper limit of the address range where we expect the
/// SNP-specific pages to reside.
///
/// We expect the boot parameters and the CPUID and secrets pages to all be
/// placed in the first 640KiB of physical memory by the Stage 0 Firmware, so we
/// can use this range to help with validation.
const MAX_ADDRESS: PhysAddr = PhysAddr::new_truncate(640 * 1024);

/// The SEV-SNP secrets page.
pub static SECRETS_PAGE: OnceCell<SecretsPage> = OnceCell::new();

/// The SEV-SNP CPUID page.
pub static CPUID_PAGE: OnceCell<CpuidPage> = OnceCell::new();

/// Wrapper for the guest-physical addresses of the secrets page and the CPUID
/// page.
pub struct SnpPageAddresses {
    pub secrets_page_address: PhysAddr,
    pub cpuid_page_address: PhysAddr,
}

/// Tries to extract the guest-physical addresses of the SEV-SNP secrets page
/// and CPUID page.
///
/// This function must only be used while the identity mapping is still in
/// place, since the pointers in the boot parameter page was constructed by the
/// Stage 0 firmware with an identity mapping.
///
/// This function will panic if the boot parameter page is not valid.
pub fn get_snp_page_addresses(info: &BootParams) -> SnpPageAddresses {
    // Check that the address of the boot parameter page looks OK.
    let base_address = VirtAddr::from_ptr(info as *const BootParams);
    // We assume an identity mapping from virtual to physical address.
    let phys = PhysAddr::new(base_address.as_u64());
    // Check that the physical address is page-aligned and in the expected range.
    assert_page_in_valid_range(phys);
    // The setup data is stored in a null-terminated linked list, so we step through
    // the list until we find an entry with the right type or reach the end.
    let mut setup_data_ptr = info.hdr.setup_data();
    while !setup_data_ptr.is_null() {
        assert_pointer_in_valid_range(setup_data_ptr);
        // Safety: we have checked that the pointer is not null and at least points to
        // memory within the expected valid range.
        let setup_data = unsafe { &*setup_data_ptr };
        let type_ = setup_data.type_;
        if type_ == SetupDataType::CCBlob {
            break;
        }
        setup_data_ptr = setup_data.next;
    }

    if setup_data_ptr.is_null() {
        panic!("couldn't find setup data of type CCBlob");
    }

    // Safety: we have checked that the pointer is not null and at least points to
    // memory within the expected valid range.
    let cc_blob_address =
        unsafe { &*(setup_data_ptr as *const CCSetupData) }.cc_blob_address as *const CCBlobSevInfo;

    assert_pointer_in_valid_range(cc_blob_address);
    // Safety: we have checked that the pointer is not null and at least points to
    // memory within the expected valid range. We also validate the magic number
    // as an additional check.
    let cc_blob = unsafe { &*cc_blob_address };
    let magic = cc_blob.magic;
    if magic != oak_linux_boot_params::CC_BLOB_SEV_INFO_MAGIC {
        panic!("CCBlobSevInfo data structure has invalid magic: {}", magic);
    }

    let cpuid_page_address = PhysAddr::new(cc_blob.cpuid_phys as u64);
    let secrets_page_address = PhysAddr::new(cc_blob.secrets_phys as u64);
    SnpPageAddresses { secrets_page_address, cpuid_page_address }
}

/// Iinitializes the references to the SEV-SNP CPUID and secrets pages.
///
/// This function will panic if it is called more than once or if page addresses
/// outside of the expected range are supplied.
///
/// Panicking throughout this functions is OK, because if any of these values
/// are invalid it means the environment was not set up correctly and we don't
/// know how to recover from that.
pub fn init_snp_pages<T: Translator>(snp_pages: SnpPageAddresses, mapper: &T) {
    // First make sure the addresses look OK: they are not null, each point to the
    // start of a 4KiB page, and within the expected memory range.
    assert_page_in_valid_range(snp_pages.cpuid_page_address);
    assert_page_in_valid_range(snp_pages.secrets_page_address);

    let cpuid_page_address = mapper
        .translate_physical(snp_pages.cpuid_page_address)
        .expect("couldn't find a valid virtual address for the CPUID page");
    // Safety: we have checked that the pointer is in the expected valid memory
    // range, not null, and 4KiB page-aligned.
    let cpuid_slice: &[u8] =
        unsafe { from_raw_parts(cpuid_page_address.as_ptr(), Size4KiB::SIZE as usize) };
    CPUID_PAGE
        .set(CpuidPage::read_from_bytes(cpuid_slice).expect("CPUID page byte slice was invalid"))
        .expect("couldn't set CPUID page");
    CPUID_PAGE.get().unwrap().validate().expect("invalid CPUID page");

    let secrets_page_address = mapper
        .translate_physical(snp_pages.secrets_page_address)
        .expect("couldn't find a valid virtual address for the secrets page");
    // Safety: we have checked that the pointer is in the expected valid memory
    // range, not null, and 4KiB page-aligned.
    let secrets_slice: &[u8] =
        unsafe { from_raw_parts(secrets_page_address.as_ptr(), Size4KiB::SIZE as usize) };
    SECRETS_PAGE
        .set(
            SecretsPage::read_from_bytes(secrets_slice)
                .expect("secrets page byte slice was invalid"),
        )
        .expect("couldn't set secrets page");
    SECRETS_PAGE.get().unwrap().validate().expect("invalid secrets page");
}

/// Panics if the physical address is not the start of a 4KiB page, null, or not
/// below the maximum expected address.
fn assert_page_in_valid_range(page: PhysAddr) {
    assert!(!page.is_null(), "address is null");
    assert_eq!(
        page.align_down(Size4KiB::SIZE),
        page,
        "address {:#018x} is not the start of a 4KiB page",
        page
    );
    assert!(
        page < MAX_ADDRESS,
        "address {:#018x} is not below the expected maximum address {:#018x}",
        page,
        MAX_ADDRESS
    );
}

/// Panics if the pointer is null or points to an address that falls outside the
/// expected range.
fn assert_pointer_in_valid_range<T>(pointer: *const T) {
    assert!(!pointer.is_null(), "pointer is null");
    let address = VirtAddr::from_ptr(pointer);
    assert!(
        address.as_u64() < MAX_ADDRESS.as_u64(),
        "pointer {:#018x} is not below the expected maximum address {:#018x}",
        address,
        MAX_ADDRESS
    );
}
