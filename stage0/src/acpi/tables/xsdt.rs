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

use x86_64::VirtAddr;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, TryFromBytes};

use crate::{
    DescriptionHeader,
    acpi::tables::{AcpiTable, Checksum, Result, signature},
};

/// A wrapper for entry addresses in XSDT table.
///
/// An entry address in XSDT has 8 bytes, but they are placed from table offset
/// 36 and not 8-byte aligned. This wrapper handles the unaligned access.
#[repr(transparent)]
#[derive(
    Copy, Clone, Debug, Default, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq,
)]
pub struct XsdtEntryPtr {
    addr: [u8; 8],
}

impl XsdtEntryPtr {
    pub fn raw_val(&self) -> u64 {
        // As per Section 5.2 in the ACPI specification 6.5,
        // Address is little endian.
        u64::from_le_bytes(self.addr)
    }

    pub fn set_addr(&mut self, value: u64) {
        value.to_le_bytes().write_to(self.addr[..].as_mut()).unwrap();
    }
}

impl From<u64> for XsdtEntryPtr {
    fn from(value: u64) -> Self {
        let mut ptr = Self::default();
        ptr.set_addr(value);
        ptr
    }
}

impl From<&XsdtEntryPtr> for VirtAddr {
    fn from(value: &XsdtEntryPtr) -> Self {
        VirtAddr::new(value.raw_val())
    }
}

impl From<&mut XsdtEntryPtr> for VirtAddr {
    fn from(value: &mut XsdtEntryPtr) -> Self {
        VirtAddr::new(value.raw_val())
    }
}

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C)]
pub struct Signature(signature::X, signature::S, signature::D, signature::T);

/// Extended System Description Table.
///
/// See Section 5.2.8 in the ACPI specification for more details.
#[derive(Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct Xsdt {
    pub header: DescriptionHeader<Signature>,
    entries: [XsdtEntryPtr],
}

impl AcpiTable for Xsdt {
    type Signature = Signature;

    fn try_from_bytes(buf: &[u8]) -> Result<(&Self, &[u8])> {
        // First, try to parse the header.
        let (header, _) =
            DescriptionHeader::<Signature>::try_ref_from_prefix(buf).map_err(|_| "invalid XSDT")?;
        // if it parses, it is a XSDT, and we can get a length from there
        if (header.length as usize) < size_of::<DescriptionHeader<Signature>>() {
            return Err("invalid XSDT");
        }
        let entries =
            (header.length as usize - size_of::<DescriptionHeader<Signature>>()) / size_of::<u64>();

        let (xsdt, tail) =
            Xsdt::try_ref_from_prefix_with_elems(buf, entries).map_err(|_| "invalid XSDT")?;

        xsdt.validate()?;

        Ok((xsdt, tail))
    }

    fn try_from_bytes_mut(buf: &mut [u8]) -> Result<(&mut Xsdt, &mut [u8])> {
        // First, try to parse the header.
        let (header, _) =
            DescriptionHeader::<Signature>::try_ref_from_prefix(buf).map_err(|_| "invalid XSDT")?;
        // if it parses, it is a XSDT, and we can get a length from there
        if (header.length as usize) < size_of::<DescriptionHeader<Signature>>() {
            return Err("invalid XSDT");
        }
        let entries =
            (header.length as usize - size_of::<DescriptionHeader<Signature>>()) / size_of::<u64>();

        let (xsdt, tail) =
            Xsdt::try_mut_from_prefix_with_elems(buf, entries).map_err(|_| "invalid XSDT")?;

        xsdt.validate()?;

        Ok((xsdt, tail))
    }

    fn header(&self) -> &DescriptionHeader<Self::Signature> {
        &self.header
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Self::Signature> {
        &mut self.header
    }

    fn validate(&self) -> Result<()> {
        if self.checksum() != 0 {
            return Err("ACPI table checksum invalid");
        }

        if !(self.header.length as usize - size_of::<DescriptionHeader<[u8; 4]>>())
            .is_multiple_of(size_of::<usize>())
        {
            return Err("XSDT invalid: entries size not a multiple of pointer size");
        }

        Ok(())
    }
}

impl Xsdt {
    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = VirtAddr> {
        self.entries.iter().map(Into::into)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut XsdtEntryPtr> {
        self.entries.iter_mut()
    }
}

// We can't derive `Debug` because of alignment issues.
impl core::fmt::Debug for Xsdt {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::result::Result<(), core::fmt::Error> {
        let holder = self.entries.to_vec();
        f.debug_struct("Xsdt").field("header", &self.header).field("entries", &holder).finish()
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;

    use super::*;

    #[test]
    pub fn test_parse_rsdt() {
        let mut buf = Vec::from(b"RSDT\x24\x00\x00\x00\x01\xB0OEMOEMAAAAAAAABBBBCCCCDDDD");

        assert_that!(Xsdt::try_from_bytes_mut(&mut buf[..]), err(anything()));
        assert_that!(Xsdt::try_from_bytes(&buf[..]), err(anything()));
    }

    #[test]
    pub fn test_empty_xsdt() {
        let mut buf = Vec::from(b"XSDT\x24\x00\x00\x00\x01\xAAOEMOEMAAAAAAAABBBBCCCCDDDD");

        let (xsdt, _) = Xsdt::try_from_bytes_mut(&mut buf[..]).unwrap();
        assert_that!(xsdt.entries, is_empty());
        let (xsdt, _) = Xsdt::try_from_bytes(&buf[..]).unwrap();
        assert_that!(xsdt.entries, is_empty());
    }

    #[test]
    pub fn test_two_entries() {
        let mut buf = Vec::from(b"XSDT\x34\x00\x00\x00\x01\x97OEMOEMAAAAAAAABBBBCCCCDDDD\x01\x00\x00\x00\x00\x00\x00\x00\x02\x00\x00\x00\x00\x00\x00\x00");

        let (xsdt, _) = Xsdt::try_from_bytes_mut(&mut buf[..]).unwrap();
        assert_that!(xsdt.entries, unordered_elements_are!(eq(&1.into()), eq(&2.into())));
        let (xsdt, _) = Xsdt::try_from_bytes(&buf[..]).unwrap();
        assert_that!(xsdt.entries, unordered_elements_are!(eq(&1.into()), eq(&2.into())));
    }
}
