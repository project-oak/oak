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

// TODO(#3703): Remove when fixed.
#![allow(clippy::extra_unused_type_parameters)]

use log::{debug, trace};
use oak_sev_guest::vmsa::VmsaPage;
use sha2::{Digest, Sha384};
use strum::FromRepr;
use x86_64::{
    PhysAddr,
    structures::paging::{PageSize, Size4KiB},
};
use zerocopy::{Immutable, IntoBytes};

/// The size of the PageInfo struct.
const PAGE_INFO_SIZE: usize = 112;

/// Implementation of the Page Info structure used for extending the measurement
/// in each step.
///
/// See table 70 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[repr(C)]
#[derive(Debug, IntoBytes, Clone, Immutable)]
pub struct PageInfo {
    /// The current measurement up to this point.
    pub digest_cur: [u8; 48],
    /// The SHA-384 digest of the contents to be measured for normal and VMSA
    /// pages, or all zeros for all other page types.
    pub contents: [u8; 48],
    /// The length of this struct in bytes.
    _length: u16,
    /// The type of page being measured.
    pub page_type: PageType,
    /// Whether the page is part of an initial migration image. For now we treat
    /// this as reserved and zero.
    _imi_page: ImiPage,
    /// Reserved. Must be 0.
    _reserved: u8,
    /// The permissions for VMPL1. For now we treat this as reserved and zero.
    _vmpl1_perms: u8,
    /// The permissions for VMPL2. For now we treat this as reserved and zero.
    _vmpl2_perms: u8,
    /// The permissions for VMPL3. For now we treat this as reserved and zero.
    _vmpl3_perms: u8,
    /// The guest-physical address of the page being measured.
    pub gpa: u64,
}

static_assertions::assert_eq_size!(PageInfo, [u8; PAGE_INFO_SIZE]);

impl PageInfo {
    pub const fn new() -> Self {
        Self {
            digest_cur: [0; 48],
            contents: [0; 48],
            _length: PAGE_INFO_SIZE as u16,
            page_type: PageType::Invalid,
            _imi_page: ImiPage::No,
            _reserved: 0,
            _vmpl1_perms: 0,
            _vmpl2_perms: 0,
            _vmpl3_perms: 0,
            gpa: 0,
        }
    }

    /// Updates the current measurement digest from a byte slice representing
    /// normal data pages.
    ///
    /// The current digest is updated separately for each 4KiB page.
    pub fn update_from_data(&mut self, data: &[u8], start_address: PhysAddr) {
        debug!(
            "Updating measurement with {} bytes starting at address {:#018x}",
            data.len(),
            start_address
        );
        assert_eq!(
            start_address,
            start_address.align_down(Size4KiB::SIZE),
            "data start address is not 4KiB-aligned."
        );
        self.page_type = PageType::Normal;
        let mut address = start_address;
        for chunk in data.chunks(Size4KiB::SIZE as usize) {
            self.gpa = address.as_u64();
            address += Size4KiB::SIZE;
            self.set_contents_from_page_bytes(chunk);
            self.update_current_digest();
        }
    }

    /// Updates the current measurement digest from a VMSA page.
    pub fn update_from_vmsa(&mut self, vmsa: &VmsaPage, start_address: PhysAddr) {
        debug!("Updating measurement with VMSA at address {:#018x}", start_address);
        self.page_type = PageType::Vmsa;
        self.gpa = start_address.as_u64();
        self.set_contents_from_page_bytes(vmsa.as_bytes());
        self.update_current_digest();
    }

    /// Updates the current measurement digest for a SEV-SNP-specific page.
    ///
    /// Measurement of these pages do not include a measurement of the content,
    /// only the metadata.
    pub fn update_from_snp_page(&mut self, page_type: PageType, start_address: PhysAddr) {
        debug!("Updating measurement with {:?} page at address {:#018x}", page_type, start_address);
        match page_type {
            PageType::Cpuid | PageType::Secrets | PageType::Unmeasured | PageType::Zero => {
                self.page_type = page_type;
                self.gpa = start_address.as_u64();
                self.contents.fill(0);
                self.update_current_digest();
            }
            _ => panic!("Unexpected page type {:?}", page_type),
        }
    }

    /// Sets the `contents` field based to the SHA-384 digest of the byte
    /// contents of a 4KiB memory page.
    ///
    /// If fewer than 4KiB of data is received the page is padded with zeros to
    /// fill the entire 4KiB area.
    fn set_contents_from_page_bytes(&mut self, page_bytes: &[u8]) {
        let byte_count = page_bytes.len();
        assert!(byte_count <= Size4KiB::SIZE as usize, "too many bytes in page");
        let mut contents_hasher = Sha384::new();
        if byte_count == Size4KiB::SIZE as usize {
            contents_hasher.update(page_bytes);
        } else {
            trace!("Only {} bytes in page, padding with zeros", byte_count);
            let mut padded_page = vec![0; Size4KiB::SIZE as usize];
            padded_page[..byte_count].copy_from_slice(page_bytes);
            contents_hasher.update(&padded_page);
        }
        let contents_digest = contents_hasher.finalize();
        self.contents[..].copy_from_slice(&contents_digest);
    }

    /// Calculates the SHA-384 digest of the struct's memory and updates
    /// `digest_cur` to the new value.
    fn update_current_digest(&mut self) {
        let mut digest_hasher = Sha384::new();
        digest_hasher.update(self.as_bytes());
        let current_digest = digest_hasher.finalize();
        self.digest_cur[..].copy_from_slice(&current_digest);
    }
}

impl Default for PageInfo {
    fn default() -> Self {
        Self::new()
    }
}

/// Whether the page is part of an initial migration image (IMI).
///
/// For now we assume we won't have any IMI pages.
#[derive(Debug, FromRepr, IntoBytes, Clone, Immutable)]
#[repr(u8)]
enum ImiPage {
    /// The page is not an IMI page.
    No = 0,
}

/// The type of page being measured.
///
/// See table 68 in <https://www.amd.com/system/files/TechDocs/56860.pdf>.
#[derive(Debug, FromRepr, IntoBytes, Clone, Copy, Immutable, PartialEq)]
#[repr(u8)]
#[allow(unused)]
pub enum PageType {
    /// Reserved value.
    Invalid = 0,
    /// The page is a normal page.
    Normal = 1,
    /// The page contains a VM state save area (VMSA) for a vCPU.
    Vmsa = 2,
    /// A page filled with zeros.
    Zero = 3,
    /// A page that is encrypted but not measured.
    Unmeasured = 4,
    /// The SEV-SNP secrets page.
    Secrets = 5,
    /// The SEV-SNP CPUID page.
    Cpuid = 6,
}
