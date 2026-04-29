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

use core::{fmt::Debug, mem::size_of};

use x86_64::VirtAddr;
use zerocopy::{FromBytes, Immutable, IntoBytes};

use crate::{
    Platform,
    acpi::tables::{Result, Rsdt, Xsdt},
};

/// ACPI Root System Description Pointer.
///
/// Used to locate either the RSDT or XSDT in memory.
///
/// See Section 5.2.5 in the ACPI specification, Version 6.5 for more details.
#[derive(FromBytes, IntoBytes, Immutable)]
#[repr(C, packed)]
pub struct Rsdp {
    /// Signature: "RSD PTR " (note the trailing space).
    signature: [u8; 8],

    /// Checksum for fields defined in the ACPI 1.0 specification.
    checksum: u8,

    /// OEM-supplied identification string.
    oemid: [u8; 6],

    /// Revision of this structure.
    ///
    /// ACPI 1.0 value is zero, ACPI 2.0 value is 2.
    revision: u8,

    /// 32-bit physical address of the RSDT.
    pub rsdt_address: u32,

    // ACPI 2.0 fields. Only valid if revision >= 2.
    // Don't make these fields public directly as we'll need to ensure the ony way to access them
    // is if revision correct.
    /// Length of the table, including the header.
    length: u32,

    /// 64-bit physical address of the XSDT.
    xsdt_address: u64,

    /// Checksum of the entire table, including both checksum fields.
    extended_checksum: u8,

    /// Reserved
    _reserved: [u8; 3],
}
static_assertions::assert_eq_size!(Rsdp, [u8; 36usize]);

impl Debug for Rsdp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let rsdt_address = self.rsdt_address;

        let mut s = f.debug_struct("Rsdp");
        s.field("signature", &self.signature)
            .field("checksum", &self.checksum)
            .field("oemid", &self.oemid)
            .field("revision", &self.revision)
            .field("rsdt_address", &rsdt_address);
        if self.revision >= 2 {
            let length = self.length;
            let xsdt_address = self.xsdt_address;
            s.field("length", &length)
                .field("xsdt_address", &xsdt_address)
                .field("extended_checksum", &self.extended_checksum)
                .field("_reserved", &self._reserved);
        }
        s.finish()
    }
}

impl Rsdp {
    pub fn validate<P: Platform>(&self) -> Result<()> {
        if &self.signature != b"RSD PTR " {
            return Err("Invalid RSDP signature");
        }
        let len = if self.revision >= 2 { self.length } else { 20 } as usize;

        if len > size_of::<Rsdp>() {
            return Err("invalid RSDP size");
        }

        let checksum = self.as_bytes()[..20].iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));

        if checksum != 0 {
            return Err("Invalid RSDP checksum");
        }

        if self.revision >= 2 {
            let checksum = self.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));

            if checksum != 0 {
                return Err("Invalid RSDP extended checksum");
            }
        }

        Ok(())
    }

    pub fn rsdt(&self) -> Option<Result<&Rsdt>> {
        if self.rsdt_address == 0 {
            None
        } else {
            Some(Rsdt::new(VirtAddr::new(self.rsdt_address as u64)))
        }
    }

    /// # Safety
    /// Caller must ensure only one mut ref exists at a time.
    pub unsafe fn rsdt_mut(&mut self) -> Option<Result<&mut Rsdt>> {
        if self.rsdt_address == 0 {
            None
        } else {
            Some(unsafe { Rsdt::new_mut(VirtAddr::new(self.rsdt_address as u64)) })
        }
    }

    pub fn xsdt(&self) -> Option<Result<&Xsdt>> {
        if self.revision < 2 || self.xsdt_address == 0 {
            None
        } else {
            Some(Xsdt::new(VirtAddr::new(self.xsdt_address)))
        }
    }

    /// # Safety
    /// Caller must ensure only one mut ref exists at a time.
    pub unsafe fn xsdt_mut(&mut self) -> Option<Result<&mut Xsdt>> {
        if self.revision < 2 || self.xsdt_address == 0 {
            None
        } else {
            Some(unsafe { Xsdt::new_mut(VirtAddr::new(self.xsdt_address)) })
        }
    }
}
