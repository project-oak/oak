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

use core::slice;

use x86_64::VirtAddr;
use zerocopy::{Immutable, IntoBytes, KnownLayout, TryFromBytes};

use crate::acpi::tables::{DescriptionHeader, Result, check_ptr_aligned, signature};

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C)]
pub struct Signature(signature::R, signature::S, signature::D, signature::T);

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

    /// # Safety
    /// Caller must ensure `addr` actually points to a RSDP (or where one could
    /// reasonably be found).
    pub unsafe fn new(addr: VirtAddr) -> Result<&'static Rsdt> {
        // Cheat: let's first see what the length is, so that we can create an array for
        // `try_from_bytes_mut`.
        let header = unsafe { &*addr.as_ptr::<DescriptionHeader<Signature>>() };

        // Safety: caller needs to guarantee this is valid.
        let (rsdt, _) = Rsdt::try_from_bytes_mut(unsafe {
            slice::from_raw_parts_mut(addr.as_mut_ptr::<u8>(), header.length as usize)
        })?;

        Ok(rsdt)
    }

    /// # Safety
    /// Caller must ensure `addr` actually points to a RSDP (or where one could
    /// reasonably be found). Caller must ensure only one mut ref exists at
    /// a time.
    pub unsafe fn new_mut(addr: VirtAddr) -> Result<&'static mut Rsdt> {
        // Cheat: let's first see what the length is, so that we can create an array for
        // `try_from_bytes_mut`.
        let header = unsafe { &*addr.as_ptr::<DescriptionHeader<Signature>>() };

        // Safety: caller needs to guarantee this is valid.
        let (rsdt, _) = Rsdt::try_from_bytes_mut(unsafe {
            slice::from_raw_parts_mut(addr.as_mut_ptr::<u8>(), header.length as usize)
        })?;

        Ok(rsdt)
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

    /// Sets checksum field so that checksum validates.
    /// To be called after modifying any of this structures's data.
    pub fn update_checksum(&mut self) {
        self.header.update_checksum();
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
}
