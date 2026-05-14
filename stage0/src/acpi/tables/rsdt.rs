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
use zerocopy::{Immutable, IntoBytes, KnownLayout, TryFromBytes};

use crate::acpi::tables::{AcpiTable, Checksum, DescriptionHeader, Result, signature};

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
#[derive(Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C, align(4))]
pub struct Rsdt {
    pub header: DescriptionHeader<Signature>,
    entries: [u32],
}

impl Checksum for Rsdt {
    fn checksum(&self) -> u8 {
        self.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs))
    }
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
        let entries =
            (header.length as usize - size_of::<DescriptionHeader<Signature>>()) / size_of::<u32>();

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
        let entries =
            (header.length as usize - size_of::<DescriptionHeader<Signature>>()) / size_of::<u32>();

        let (rsdt, tail) = Rsdt::try_mut_from_prefix_with_elems(buf, entries)
            .map_err(|_| "invalid RSDT elements")?;

        rsdt.validate()?;

        Ok((rsdt, tail))
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Self::Signature> {
        &mut self.header
    }

    fn validate(&self) -> Result<()> {
        if self.checksum() != 0 {
            return Err("ACPI table checksum invalid");
        }

        if !(self.header.length as usize - size_of::<DescriptionHeader<[u8; 4]>>())
            .is_multiple_of(size_of::<u32>())
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
            length: (size_of::<DescriptionHeader<Signature>>() + num * size_of::<u32>()) as u32,
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

        // Use u32 instead of u8, as that guarantees the alignment is correct.
        let mut buf =
            vec![0u32; size_of::<DescriptionHeader<Signature>>() / size_of::<u32>() + num]
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
        self.entries.iter().map(|&entry| VirtAddr::new(entry as u64))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut u32> {
        self.entries.iter_mut()
    }
}

impl Index<usize> for Rsdt {
    type Output = u32;

    fn index(&self, index: usize) -> &Self::Output {
        &self.entries[index]
    }
}

impl IndexMut<usize> for Rsdt {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.entries[index]
    }
}

// Slice DSTs confuse googletest ([u32] is not `Sized`), so we have to do some
// things by hand.
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
        assert_that!(rsdt.entries, unordered_elements_are!(eq(&1), eq(&2)));
        let (rsdt, _) = Rsdt::try_from_bytes(&buf[..]).unwrap();
        assert_that!(rsdt.entries, unordered_elements_are!(eq(&1), eq(&2)));
    }

    #[test]
    pub fn test_new_rsdt() {
        let mut rsdt = Rsdt::new_with_size(1);
        let old_checksum = rsdt.header.checksum;
        rsdt.entries[0] = 0x01020304;
        rsdt.update_checksum();

        assert_that!(old_checksum, not(eq(rsdt.header.checksum)));

        let buf = Vec::from(b"RSDT\x28\x00\x00\x00\x00\x91\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x04\x03\x02\x01");
        assert_that!(rsdt.as_bytes(), eq(buf));
    }
}
