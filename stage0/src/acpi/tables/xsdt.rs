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

use core::{
    marker::PhantomData,
    ops::{Deref, DerefMut, Range},
    slice,
};

use x86_64::VirtAddr;
use zerocopy::IntoBytes;

use crate::{
    DescriptionHeader,
    acpi::tables::{Result, check_ptr_aligned},
};

/// A wrapper for entry addresses in XSDT table.
///
/// An entry address in XSDT has 8 bytes, but they are placed from table offset
/// 36 and not 8-byte aligned. This wrapper handles the unaligned access.
#[repr(C)]
pub struct XsdtEntryPtr<'a> {
    addr: [u8; 8],
    _phantom: PhantomData<&'a DescriptionHeader>,
}

impl XsdtEntryPtr<'_> {
    pub fn raw_val(&self) -> u64 {
        // As per Section 5.2 in the ACPI specification 6.5,
        // Address is little endian.
        u64::from_le_bytes(self.addr)
    }

    pub fn set_addr(&mut self, value: u64) {
        value.to_le_bytes().write_to(self.addr[..].as_mut()).unwrap();
        self.validate().expect("XsdtEntryPtr validate failed on set_addr");
    }
}

impl Deref for XsdtEntryPtr<'_> {
    type Target = DescriptionHeader;

    fn deref(&self) -> &DescriptionHeader {
        let ptr = self.raw_val() as *const DescriptionHeader;
        check_ptr_aligned(ptr);
        // Safety: the address has been validated in Xsdt::validate().
        unsafe { &*ptr }
    }
}

impl DerefMut for XsdtEntryPtr<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let ptr = self.raw_val() as *mut DescriptionHeader;
        check_ptr_aligned(ptr);
        // Safety: the address has been validated in Xsdt::validate().
        unsafe { &mut *ptr }
    }
}

/// Extended System Description Table.
///
/// See Section 5.2.8 in the ACPI specification for more details.
#[derive(Debug)]
#[repr(C, packed)]
pub struct Xsdt {
    pub header: DescriptionHeader,
    // The XSDT contains an array of pointers to other tables, but unfortunately this can't be
    // expressed in Rust.
}

impl Xsdt {
    const SIGNATURE: &'static [u8; 4] = b"XSDT";

    pub fn new(addr: VirtAddr) -> Result<&'static Xsdt> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let xsdt = unsafe { &*addr.as_ptr::<Xsdt>() };
        xsdt.validate()?;
        Ok(xsdt)
    }

    /// # Safety
    ///
    /// Caller must ensure only one mut ref exists at a time.
    pub unsafe fn new_mut(addr: VirtAddr) -> Result<&'static mut Xsdt> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let xsdt = unsafe { &mut *addr.as_mut_ptr::<Xsdt>() };
        xsdt.validate()?;
        Ok(xsdt)
    }

    /// Returns the address range where this table is located.
    pub fn addr_range(&self) -> Range<usize> {
        let base = self as *const _ as usize;
        base..base + self.header.length as usize
    }

    /// Sets checksum field so that checksum validates.
    /// To be called after modifying any of this structures's data.
    pub fn update_checksum(&mut self) {
        self.header.update_checksum();
    }

    /// Finds a table based on the signature, if it is present.
    /// Finds a validated XSDT pointer in this RSDT, by its signature, if
    /// present. All `XsdtEntryPtr`s seen on the way are validated
    /// too and errors propagated. Returns:
    ///   - Ok(None) -> Search went without errors, entry not found.
    ///   - Ok(Some(&XsdtEntryPtr)) -> No errors, entry found.
    ///   - Err(e) -> An XsdtEntryPtr seen during search failed validation.
    pub fn get(&self, signature: &[u8; 4]) -> Result<Option<&DescriptionHeader>> {
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
    pub fn entry_ptrs(&self) -> impl Iterator<Item = Result<&XsdtEntryPtr<'_>>> {
        self.entries_arr().iter().map(|xsdt_ptr| {
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
    pub fn get_entry_mut(&mut self, signature: &[u8; 4]) -> Result<Option<&mut XsdtEntryPtr<'_>>> {
        self.validate()?;
        let maybe_found = self.entries_arr_mut().iter_mut().find_map(|xsdt_entry_ptr| {
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

    fn entries_arr(&self) -> &[XsdtEntryPtr<'_>] {
        let entries_base_ptr =
            (self as *const _ as usize + size_of::<DescriptionHeader>()) as *const XsdtEntryPtr;
        check_ptr_aligned(entries_base_ptr);
        // Safety: we've validated that the address and length makes sense in
        // `validate()`. XsdtEntryPtr is 1-byte aligned.
        unsafe {
            slice::from_raw_parts(
                entries_base_ptr,
                (self.header.length as usize - size_of::<DescriptionHeader>())
                    / size_of::<XsdtEntryPtr>(),
            )
        }
    }

    fn entries_arr_mut(&mut self) -> &mut [XsdtEntryPtr<'_>] {
        let entries_base_ptr =
            (self as *const _ as usize + size_of::<DescriptionHeader>()) as *mut XsdtEntryPtr;
        check_ptr_aligned(entries_base_ptr);
        // Safety: we've validated that the address and length makes sense in
        // `validate()`. XsdtEntryPtr is 1-byte aligned.
        unsafe {
            slice::from_raw_parts_mut(
                entries_base_ptr,
                (self.header.length as usize - size_of::<DescriptionHeader>())
                    / size_of::<XsdtEntryPtr>(),
            )
        }
    }

    pub fn validate(&self) -> Result<()> {
        self.header.validate()?;

        if self.header.signature != *Self::SIGNATURE {
            return Err("Invalid signature for XSDT table");
        }

        if !(self.header.length as usize - size_of::<DescriptionHeader>())
            .is_multiple_of(size_of::<usize>())
        {
            return Err("XSDT invalid: entries size not a multiple of pointer size");
        }

        Ok(())
    }
}
