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

use core::ops::{Deref, DerefMut};

use x86_64::VirtAddr;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, TryFromBytes};

use crate::{
    DescriptionHeader,
    acpi::tables::{AcpiTable, Checksum, Result, check_ptr_aligned, signature},
    acpi::acpi_memory_contains,
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

impl Deref for XsdtEntryPtr {
    type Target = DescriptionHeader<[u8; 4]>;

    fn deref(&self) -> &DescriptionHeader<[u8; 4]> {
        let addr = self.raw_val() as usize;
        // SECURITY: `addr` is a u64 the untrusted host wrote into the XSDT
        // contents via fw_cfg / AddPointer. The previous comment claimed
        // validation happened in `Xsdt::validate()`, but that function does
        // not validate entry-pointer targets. Fail closed by panicking if
        // the address does not lie inside an ACPI memory region this stage0
        // controls; boot failure is the correct outcome for malformed input.
        if !acpi_memory_contains(addr, size_of::<DescriptionHeader<[u8; 4]>>()) {
            panic!("XSDT entry points outside ACPI memory: {addr:#x}");
        }
        let ptr = addr as *const DescriptionHeader<[u8; 4]>;
        check_ptr_aligned(ptr);
        // Safety: we just validated that the pointer lies within ACPI memory
        // we own, and `check_ptr_aligned` confirms alignment.
        unsafe { &*ptr }
    }
}

impl DerefMut for XsdtEntryPtr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let addr = self.raw_val() as usize;
        // SECURITY: see `Deref::deref` above.
        if !acpi_memory_contains(addr, size_of::<DescriptionHeader<[u8; 4]>>()) {
            panic!("XSDT entry points outside ACPI memory: {addr:#x}");
        }
        let ptr = addr as *mut DescriptionHeader<[u8; 4]>;
        check_ptr_aligned(ptr);
        // Safety: as above.
        unsafe { &mut *ptr }
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
    pub entries: [XsdtEntryPtr],
}

impl Checksum for Xsdt {
    fn checksum(&self) -> u8 {
        self.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs))
    }
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
    /// Finds a table based on the signature, if it is present.
    /// Finds a validated XSDT pointer in this RSDT, by its signature, if
    /// present. All `XsdtEntryPtr`s seen on the way are validated
    /// too and errors propagated. Returns:
    ///   - Ok(None) -> Search went without errors, entry not found.
    ///   - Ok(Some(&XsdtEntryPtr)) -> No errors, entry found.
    ///   - Err(e) -> An XsdtEntryPtr seen during search failed validation.
    pub fn get(&self, signature: &[u8; 4]) -> Result<Option<&DescriptionHeader<[u8; 4]>>> {
        self.validate()?;
        let maybe_found = self.entry_ptrs().find(|ptr_or_err| match ptr_or_err {
            Err(_) => true, // Found an error, stop search and propagate.
            Ok(entry_ptr) => entry_ptr.signature == *signature,
        });
        match maybe_found {
            None => Ok(None),
            Some(Err(e)) => Err(e),
            Some(Ok(entry_ptr)) => Ok(Some(entry_ptr)),
        }
    }

    /// Returns an iterator over the entry pointers in this XSDT, validated.
    pub fn entry_ptrs(&self) -> impl Iterator<Item = Result<&XsdtEntryPtr>> {
        self.entries.iter().map(|xsdt_ptr| {
            xsdt_ptr.validate()?;
            Ok(xsdt_ptr)
        })
    }

    /// Mutable finds a validated header based on the signature on the RSDT, if
    /// present. All headers seen on the way are validated too and errors
    /// propagated. Returns:
    ///   - Ok(None) -> Search went without errors, entry not found.
    ///   - Ok(Some(EntryPairMut)) -> Search went without errors, entry found
    ///     and returned.
    ///   - Err(e) -> A DescriptionHeader seen during search failed validation.
    pub fn get_entry_mut(&mut self, signature: &[u8; 4]) -> Result<Option<&mut XsdtEntryPtr>> {
        self.validate()?;
        let maybe_found = self.entries.iter_mut().find_map(|xsdt_entry_ptr| {
            match xsdt_entry_ptr.validate() {
                Err(e) => Some(Err(e)), // Found an error, stop search and propoagate.
                Ok(()) => {
                    if xsdt_entry_ptr.signature == *signature {
                        Some(Ok(xsdt_entry_ptr))
                    } else {
                        None
                    }
                }
            }
        });
        match maybe_found {
            None => Ok(None),
            Some(Err(e)) => Err(e),
            Some(Ok(entry)) => Ok(Some(entry)),
        }
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
