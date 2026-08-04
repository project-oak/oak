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

use alloc::{boxed::Box, vec};
use core::{
    assert,
    iter::Iterator,
    ops::{Index, IndexMut},
};

use x86_64::VirtAddr;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, TryFromBytes};

use crate::acpi::tables::{AcpiTable, Checksum, DescriptionHeader, Result, signature};

/// A wrapper for entry addresses in the RSDT table.
///
/// An entry address in the RSDT has 4 bytes, but the table itself is not
/// guaranteed to be 4-byte aligned, so neither are the entries. This wrapper
/// handles the unaligned access.
#[repr(transparent)]
#[derive(
    Copy, Clone, Debug, Default, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq,
)]
pub struct RsdtEntryPtr {
    addr: [u8; 4],
}

impl From<RsdtEntryPtr> for u32 {
    fn from(value: RsdtEntryPtr) -> Self {
        // As per Section 5.2 in the ACPI specification 6.5,
        // Address is little endian.
        u32::from_le_bytes(value.addr)
    }
}

impl From<u32> for RsdtEntryPtr {
    fn from(value: u32) -> Self {
        Self { addr: value.to_le_bytes() }
    }
}

impl From<&RsdtEntryPtr> for VirtAddr {
    fn from(value: &RsdtEntryPtr) -> Self {
        VirtAddr::new(u32::from(*value) as u64)
    }
}

impl From<&mut RsdtEntryPtr> for VirtAddr {
    fn from(value: &mut RsdtEntryPtr) -> Self {
        VirtAddr::new(u32::from(*value) as u64)
    }
}

impl TryFrom<VirtAddr> for RsdtEntryPtr {
    type Error = &'static str;

    /// RSDT entries are 32-bit addresses, so the address has to fit in a `u32`.
    fn try_from(value: VirtAddr) -> Result<Self> {
        let addr: u32 =
            value.as_u64().try_into().map_err(|_| "address does not fit in a RSDT entry")?;
        Ok(addr.into())
    }
}

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C)]
pub struct Signature(signature::R, signature::S, signature::D, signature::T);
static_assertions::assert_eq_size!(DescriptionHeader<Signature>, [u8; 36usize]);

/// Root System Description Table.
///
/// This is a "slice DST" type as it contains a (unknown) amount of entries.
///
/// See Section 5.2.7 in the ACPI specification for more details.
#[derive(Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct Rsdt {
    pub header: DescriptionHeader<Signature>,
    entries: [RsdtEntryPtr],
}

impl AcpiTable for Rsdt {
    type Signature = Signature;

    fn try_from_bytes(buf: &[u8]) -> Result<(&Self, &[u8])> {
        // First, try to parse the header.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid RSDT header")?;
        // if it parses, it is a RSDT, and we can get a length from there
        if (header.length as usize) < size_of::<DescriptionHeader<Signature>>() {
            return Err("invalid RSDT");
        }
        let entries = (header.length as usize - size_of::<DescriptionHeader<Signature>>())
            / size_of::<RsdtEntryPtr>();

        let (rsdt, tail) = Rsdt::try_ref_from_prefix_with_elems(buf, entries)
            .map_err(|_| "invalid RSDT elements")?;

        rsdt.validate()?;

        Ok((rsdt, tail))
    }

    fn try_from_bytes_mut(buf: &mut [u8]) -> Result<(&mut Rsdt, &mut [u8])> {
        // First, try to parse the header.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid RSDT header")?;
        // if it parses, it is a RSDT, and we can get a length from there
        if (header.length as usize) < size_of::<DescriptionHeader<Signature>>() {
            return Err("invalid RSDT");
        }
        let entries = (header.length as usize - size_of::<DescriptionHeader<Signature>>())
            / size_of::<RsdtEntryPtr>();

        let (rsdt, tail) = Rsdt::try_mut_from_prefix_with_elems(buf, entries)
            .map_err(|_| "invalid RSDT elements")?;

        rsdt.validate()?;

        Ok((rsdt, tail))
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
            .is_multiple_of(size_of::<RsdtEntryPtr>())
        {
            return Err("RSDT invalid: entries size not a multiple of pointer size");
        }

        Ok(())
    }
}

impl Rsdt {
    pub fn new_with_size(num: usize) -> Box<Rsdt> {
        let mut header = DescriptionHeader::<Signature> {
            signature: Signature::default(),
            length: (size_of::<DescriptionHeader<Signature>>() + num * size_of::<RsdtEntryPtr>())
                as u32,
            revision: 0,
            checksum: 0,
            oem_id: [0; 6],
            oem_table_id: [0; 8],
            oem_revision: 0,
            creator_id: 0,
            creator_revision: 0,
        };
        // For now, we can't call `header.update_checksum()` here as that uses unsafe
        // code that references `length` and would read beyond the buffer. However, as
        // the zeroes in the entries slice won't change the checksum, for now we can do
        // it by hand here.
        header.checksum = header
            .checksum
            .wrapping_sub(header.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs)));

        // `Rsdt` is byte-aligned, so a byte buffer matches the layout (and thus the
        // deallocation layout of the `Box` we hand out) exactly.
        let mut buf =
            vec![0u8; size_of::<DescriptionHeader<Signature>>() + num * size_of::<RsdtEntryPtr>()]
                .into_boxed_slice();
        header.write_to_prefix(buf.as_mut_bytes()).unwrap();

        let buf = Box::leak(buf);
        // This `unwrap()` and assertion should never fail.
        let (rsdt, suffix) = Rsdt::try_from_bytes_mut(buf.as_mut_bytes()).unwrap();
        assert!(suffix.is_empty());

        // Safety: the memory was leaked from a Box; the pointer does not change, and
        // the size does not change.
        unsafe { Box::from_raw(rsdt) }
    }

    pub const fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub const fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = VirtAddr> {
        self.entries.iter().map(Into::into)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut RsdtEntryPtr> {
        self.entries.iter_mut()
    }
}

impl Index<usize> for Rsdt {
    type Output = RsdtEntryPtr;

    fn index(&self, index: usize) -> &Self::Output {
        &self.entries[index]
    }
}

impl IndexMut<usize> for Rsdt {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.entries[index]
    }
}

// We can't derive `Debug` because of alignment issues.
impl core::fmt::Debug for Rsdt {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::result::Result<(), core::fmt::Error> {
        let holder = self.entries.to_vec();
        f.debug_struct("Rsdt").field("header", &self.header).field("entries", &holder).finish()
    }
}

// Slice DSTs confuse googletest ([RsdtEntryPtr] is not `Sized`), so we have to
// do some things by hand.
#[cfg(test)]
mod tests {
    use std::vec::Vec;

    use googletest::prelude::*;

    use super::*;

    #[test]
    pub fn test_empty_rsdt() {
        let mut buf = Vec::from(b"RSDT\x24\x00\x00\x00\x01\xB0OEMOEMAAAAAAAABBBBCCCCDDDD");

        let (rsdt, _) = Rsdt::try_from_bytes_mut(&mut buf[..]).unwrap();
        assert_that!(rsdt.entries, is_empty());
        let (rsdt, _) = Rsdt::try_from_bytes(&buf[..]).unwrap();
        assert_that!(rsdt.entries, is_empty());
    }

    #[test]
    pub fn test_two_entries() {
        let mut buf = Vec::from(b"RSDT\x2C\x00\x00\x00\x01\xA5OEMOEMAAAAAAAABBBBCCCCDDDD\x01\x00\x00\x00\x02\x00\x00\x00");

        let (rsdt, _) = Rsdt::try_from_bytes_mut(&mut buf[..]).unwrap();
        assert_that!(rsdt.entries, unordered_elements_are!(eq(&1.into()), eq(&2.into())));
        let (rsdt, _) = Rsdt::try_from_bytes(&buf[..]).unwrap();
        assert_that!(rsdt.entries, unordered_elements_are!(eq(&1.into()), eq(&2.into())));
    }

    /// The RSDT is not guaranteed to be 4-byte aligned, so parsing must work
    /// even if the table starts at an odd address.
    #[test]
    pub fn test_unaligned_entries() {
        // Prefix the table with one byte so that the table itself can't be 4-byte
        // aligned, no matter where the buffer itself was allocated.
        let mut buf = Vec::from(b"\x00RSDT\x2C\x00\x00\x00\x01\xA5OEMOEMAAAAAAAABBBBCCCCDDDD\x01\x00\x00\x00\x02\x00\x00\x00");

        let (rsdt, _) = Rsdt::try_from_bytes_mut(&mut buf[1..]).unwrap();
        assert_that!(rsdt.entries, unordered_elements_are!(eq(&1.into()), eq(&2.into())));
        let (rsdt, _) = Rsdt::try_from_bytes(&buf[1..]).unwrap();
        assert_that!(rsdt.entries, unordered_elements_are!(eq(&1.into()), eq(&2.into())));
    }

    #[test]
    pub fn test_new_rsdt() {
        let mut rsdt = Rsdt::new_with_size(1);
        let old_checksum = rsdt.header.checksum;
        rsdt[0] = 0x01020304.into();
        rsdt.update_checksum();

        assert_that!(old_checksum, not(eq(rsdt.header.checksum)));

        let buf = Vec::from(b"RSDT\x28\x00\x00\x00\x00\x91\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x03\x02\x01");
        assert_that!(rsdt.as_bytes(), eq(buf));
    }
}
