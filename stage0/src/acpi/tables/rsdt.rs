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

use crate::acpi::tables::{DescriptionHeader, Result, check_ptr_aligned};

/// Root System Description Table.
///
/// See Section 5.2.7 in the ACPI specification for more details.
#[derive(Debug)]
#[repr(C, align(4))]
pub struct Rsdt {
    pub header: DescriptionHeader<[u8; 4]>,
    // The RSDT contains an array of pointers to other tables, but unfortunately this can't be
    // expressed in Rust. By adding an zero size array here, we can make sure that `entries_arr`
    // always aligns at 4. Otherwise, the compiler will throw an error.
    entries_arr: [u32; 0],
}

pub type RsdtEntryPairMut<'a> = (&'a mut u32, &'a mut DescriptionHeader<[u8; 4]>);

impl Rsdt {
    const SIGNATURE: &'static [u8; 4] = b"RSDT";

    pub fn new(addr: VirtAddr) -> Result<&'static Rsdt> {
        // Safety: we're checking that it's a valid RSDT in `validate()`.
        let rsdt = unsafe { &*addr.as_ptr::<Rsdt>() };
        rsdt.validate()?;
        Ok(rsdt)
    }

    /// # Safety
    /// Caller must ensure only one mut ref exists at a time.
    pub unsafe fn new_mut(addr: VirtAddr) -> Result<&'static mut Rsdt> {
        // # Safety: we're checking that it's a valid RSDT in `validate()`.
        let rsdt = unsafe { &mut *addr.as_mut_ptr::<Rsdt>() };
        rsdt.validate()?;
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
        self.entries_arr().iter().map(|&entry| {
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
        self.entries_arr_mut().iter_mut().map(|addr| {
            let header_ptr = *addr as usize as *mut DescriptionHeader<[u8; 4]>;
            check_ptr_aligned(header_ptr);
            // # Safety we are validating the header.
            let header = unsafe { header_ptr.as_mut().ok_or("Address 0x0 in RSDT")? };
            header.validate()?;
            Ok((addr, header))
        })
    }

    fn entries_arr(&self) -> &[u32] {
        let entries_base_ptr = &self.entries_arr as *const u32;
        check_ptr_aligned(entries_base_ptr);
        // Safety: we've validated that the address and length makes sense in
        // `validate()`.
        unsafe {
            slice::from_raw_parts(
                entries_base_ptr,
                (self.header.length as usize - size_of::<DescriptionHeader<[u8; 4]>>())
                    / size_of::<u32>(),
            )
        }
    }

    fn entries_arr_mut(&mut self) -> &mut [u32] {
        let entries_base_ptr = &self.entries_arr as *const _ as *mut u32;
        check_ptr_aligned(entries_base_ptr);
        // Safety: we've validated that the address and length makes sense in
        // `validate()`.
        unsafe {
            slice::from_raw_parts_mut(
                entries_base_ptr,
                (self.header.length as usize - size_of::<DescriptionHeader<[u8; 4]>>())
                    / size_of::<u32>(),
            )
        }
    }

    fn validate(&self) -> Result<()> {
        self.header.validate()?;

        if self.header.signature != *Self::SIGNATURE {
            return Err("Invalid signature for RSDT table");
        }

        if !(self.header.length as usize - size_of::<DescriptionHeader<[u8; 4]>>())
            .is_multiple_of(size_of::<u32>())
        {
            return Err("RSDT invalid: entries size not a multiple of pointer size");
        }

        Ok(())
    }
}
