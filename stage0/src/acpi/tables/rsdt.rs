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
use core::assert;

use zerocopy::{Immutable, IntoBytes, KnownLayout, TryFromBytes};

use crate::acpi::tables::{DescriptionHeader, Result, check_ptr_aligned, signature};

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
    pub entries: [u32],
}

pub type RsdtEntryPairMut<'a> = (&'a mut u32, &'a mut DescriptionHeader<[u8; 4]>);

impl Rsdt {
    pub fn try_from_bytes_mut(buf: &mut [u8]) -> Result<(&mut Rsdt, &mut [u8])> {
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

    fn checksum(&self) -> u8 {
        self.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs))
    }

    pub fn update_checksum(&mut self) {
        self.header.checksum = self.header.checksum.wrapping_sub(self.checksum());
    }

    /// Finds a validated header pointed at by this RSDT, by its
    /// signature, if present. All headers seen on the way are validated too
    /// and errors propagated. Returns:
    ///   - Ok(None) -> Search went without errors, entry not found.
    ///   - Ok(Some(&DescriptionHeader)) -> No errors, entry found.
    ///   - Err(e) -> A DescriptionHeader seen during search failed validation.
    pub fn get(&self, signature: &[u8; 4]) -> Result<Option<&DescriptionHeader<[u8; 4]>>> {
        self.validate()?;
        let maybe_found = self.entry_headers().find(|hdr_or_err| match hdr_or_err {
            Err(_) => true, // Found an error, stop search and propagate.
            Ok(header) => header.signature == *signature,
        });
        match maybe_found {
            None => Ok(None),
            Some(Err(e)) => Err(e),
            Some(Ok(header)) => Ok(Some(header)),
        }
    }

    /// Returns an iterator over the headers pointed at by this RSDT, validated.
    pub fn entry_headers(&self) -> impl Iterator<Item = Result<&DescriptionHeader<[u8; 4]>>> {
        self.entries.iter().map(|&entry| {
            let ptr: *const DescriptionHeader<[u8; 4]> =
                entry as usize as *const DescriptionHeader<[u8; 4]>;
            check_ptr_aligned(ptr);
            // Safety: we are validating the header.
            let header = unsafe { &*ptr };
            header.validate()?;
            Ok(header)
        })
    }

    /// Mutable finds a validated header pointed at by this RSDT, by its
    /// signature, if present. All headers seen on the way are validated too
    /// and errors propagated. Returns:
    ///   - Ok(None) -> Search went without errors, entry not found.
    ///   - Ok(Some(EntryPairMut)) -> Search went without errors, entry found.
    ///   - Err(e) -> A DescriptionHeader seen during search failed validation.
    pub fn get_entry_pair_mut(
        &mut self,
        signature: &[u8; 4],
    ) -> Result<Option<RsdtEntryPairMut<'_>>> {
        self.validate()?;
        let maybe_found: Option<Result<RsdtEntryPairMut>> =
            self.entry_headers_mut().find(|hdr_or_err| match hdr_or_err {
                Err(_) => true, // Found an error, stop search and propoagate.
                Ok((_addr, header)) => header.signature == *signature,
            });
        match maybe_found {
            None => Ok(None),
            Some(Err(e)) => Err(e),
            Some(Ok(result)) => Ok(Some(result)),
        }
    }

    fn entry_headers_mut(&mut self) -> impl Iterator<Item = Result<RsdtEntryPairMut<'_>>> {
        self.entries.iter_mut().map(|addr| {
            let header_ptr = *addr as usize as *mut DescriptionHeader<[u8; 4]>;
            check_ptr_aligned(header_ptr);
            // # Safety we are validating the header.
            let header = unsafe { header_ptr.as_mut().ok_or("Address 0x0 in RSDT")? };
            header.validate()?;
            Ok((addr, header))
        })
    }

    fn validate(&self) -> Result<()> {
        self.header.validate()?;

        if !(self.header.length as usize - size_of::<DescriptionHeader<[u8; 4]>>())
            .is_multiple_of(size_of::<u32>())
        {
            return Err("RSDT invalid: entries size not a multiple of pointer size");
        }

        Ok(())
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
    }

    #[test]
    pub fn test_two_entries() {
        let mut buf = Vec::from(b"RSDT\x2C\x00\x00\x00\x01\xA5OEMOEMAAAAAAAABBBBCCCCDDDD\x01\x00\x00\x00\x02\x00\x00\x00");

        let (rsdt, _) = Rsdt::try_from_bytes_mut(&mut buf[..]).unwrap();
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
