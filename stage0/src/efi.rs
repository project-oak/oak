//
// Copyright 2023 The Project Oak Authors
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

//! Basic data structures for EFI.
//!
//! IMPORTANT: We do not claim any compatibility with EFI. These data structures are here just in
//! hopes that we'll be able to fool Linux enough not to scan a non-validated range of memory for
//! DMI data when booting under SEV-SNP.
//!
//! We do not plan to support any EFI services in stage0.

use alloc::boxed::Box;
use core::mem;

use zerocopy::AsBytes;

use crate::{BootAllocator, BOOT_ALLOC};

type EfiHandle = usize;

/// EFI table header.
///
/// See Section 4.2.1. EFI_TABLE_HEADER in the UEFI Specification 2.10 for more details.
#[repr(C)]
#[derive(AsBytes, Default)]
pub struct EfiTableHeader {
    /// Identifies the type of table that follows.
    pub signature: u64,

    /// Revsion of the EFI Specification to which this table conforms.
    pub revision: u32,

    /// The size, in bytes, of the entire table, including the header.
    pub header_size: u32,

    /// 32-bit CRC of the entire table.
    pub crc32: u32,

    /// Reserved, must be zero.
    pub reserved: u32,
}

impl EfiTableHeader {
    const EFI_2_100_SYSTEM_TABLE_REVISION: u32 = ((2 << 16) | (100));
}

/// EFI System Table.
///
/// See Section 4.3.1. EFI_SYSTEM_TABLE in the UEFI Specification 2.10 for more details.
#[repr(C)]
#[derive(AsBytes)]
pub struct EfiSystemTable {
    /// Table header for the EFI System Table.
    pub header: EfiTableHeader,

    /// Pointer to a null-terminated string that identifies the vendor of the firmware.
    pub firmware_vendor: usize,

    /// Vendor-specific value that identifies the revision of the firmware.
    pub firmware_revision: u32,

    // Padding to placate `zerocopy::AsBytes.` This does not change the size of the data structure,
    // as we're `repr(C)` and the padding would be added implicitly anyway. (Verified by the static
    // assertion just after the data structure.)
    _pad: u32,

    pub console_in_handle: EfiHandle,
    pub con_in: usize,
    pub console_out_handle: EfiHandle,
    pub con_out: usize,
    pub std_err_handle: EfiHandle,
    pub std_err: usize,
    pub runtime_services: usize,
    pub boot_services: usize,

    /// Number of system configuration tables in the `config_table`.
    pub num_entries: usize,

    /// Pointer to the system configuration tables.
    pub config_table: usize,
}
static_assertions::assert_eq_size!(EfiSystemTable, [u8; 120usize]);

impl EfiSystemTable {
    const SIGNATURE: u64 = 0x5453595320494249;

    const CCITT32_CRC: crc::Crc<u32> = crc::Crc::<u32>::new(&crc::CRC_32_CKSUM);

    pub fn checksum(&self) -> u32 {
        Self::CCITT32_CRC.checksum(self.as_bytes())
    }
}

impl Default for EfiSystemTable {
    fn default() -> Self {
        let mut table = Self {
            header: EfiTableHeader {
                signature: Self::SIGNATURE,
                revision: EfiTableHeader::EFI_2_100_SYSTEM_TABLE_REVISION,
                header_size: mem::size_of::<Self>().try_into().unwrap(),
                ..EfiTableHeader::default()
            },
            firmware_vendor: 0,
            firmware_revision: 0,
            _pad: 0,
            console_in_handle: 0,
            con_in: 0,
            console_out_handle: 0,
            con_out: 0,
            std_err_handle: 0,
            std_err: 0,
            runtime_services: 0,
            boot_services: 0,
            num_entries: 0,
            config_table: 0,
        };
        table.header.crc32 = table.checksum();
        table
    }
}

/// Create a fake placeholder EFI System Table and put a pointer to that in the zero page.
pub fn create_efi_skeleton() -> Box<EfiSystemTable, &'static BootAllocator> {
    // We don't set anything in the table itself. As said, it's a fake table.
    Box::new_in(EfiSystemTable::default(), &BOOT_ALLOC)
}
