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

//! Defines ACPI structures based on ACPI specification.
//! You can find this specification here:
//! https://uefi.org/htmlspecs/ACPI_Spec_6_4_html/05_ACPI_Software_Programming_Model/ACPI_Software_Programming_Model.html
//!
//! ACPI tables are located in the first 1KB of the EBDA (Extended Bios Data
//! Area) or in the BIOS read-only memory space between 0E0000h and 0FFFFFh. The
//! basic structure of ACPI tables is as follows:
//!
//! - RSDP (Root System Descriptor Pointer) is a structure (not a pointer)
//!   described in ACPI Spec section 5.2.5. It's location is hardcoded by the
//!   firmware, and it's in the first 1KB of the EBDA. In our case we provide
//!   the location using the linker section ".ebda.rsdp" (see layout.ld files).
//!   The RSDP contains optional pointers to an RSDT and an XSDT. Version 1 RSDP
//!   uses an RSDT while v2 may use an XSDT.
//!   - RSDT (Root System Description Table) - ACPI Spec section 5.2.7 contains
//!     a header (our type: `DescriptionHeader`) and a variable number of 4-byte
//!     pointers to the headers (also `DescriptionHeader`) of substructures
//!     described below.
//!   - XSDT (Extended System Description Table) - ACPI Spec section 5.2.8
//!     contains a header (also `DescriptionHeader`) and a variable number of
//!     8-byte pointers to the headers (also `DescriptionHeader`) of
//!     substrucutres described below.
//!
//!     - RSDT and XSDT entry pointers point to a number of possible
//!       substructures, each with a 4-byte signature, listed in tables 5.5 and
//!       5.6 of ACPI Spec.
//!     - One such substracture is a MADT (Multiple APIC Description Table),
//!       with signature "APIC", described in ACPI Spec section 5.2.12. A MADT
//!       (our type: `Madt`) contains a header (also a `DescriptionHeader`), a
//!       coupld more fields, plus a variable number of variable length
//!       "Interrupt Controller Structures". These ICSs can't be represented in
//!       Rust, so they're parsed dynamically (remember that the initial content
//!       of ACPI tables is given to use by the VMM).
//!
//!       - In its "Interrupt Controller Structure" entries (our type:
//!         `ControllerHeader`), a MADT can contain multiple substructures, the
//!         type of each identified by a 1-byte integer (as opposed to a 4-byte
//!         signature)
//!       - We are only interested in a subset of such substructures, like
//!         LocalApic (type=0, section 5.2.12.2), LocalX2Apic(type=9, section
//!         5.2.12.12), and MultiprocessorWakeupStructure (type=0x10, section
//!         5.2.12.19). This last one is used to hand over APs to the OS.
//!
//! Collectively, these structures are referred to as "the ACPI tables".

use alloc::vec::Vec;
use core::{
    any::type_name,
    fmt::{Debug, Display},
    marker::PhantomData,
    mem::size_of,
    ops::{Deref, DerefMut, Range},
    slice,
};

use bitflags::bitflags;
use x86_64::VirtAddr;
use zerocopy::{FromBytes, Immutable, IntoBytes};

use crate::{acpi::HIGH_MEMORY_ALLOCATOR, Platform};

type ResultStaticErr<T> = Result<T, &'static str>;

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
    pub fn validate<P: Platform>(&self) -> ResultStaticErr<()> {
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

    pub fn rsdt(&self) -> Option<ResultStaticErr<&Rsdt>> {
        if self.rsdt_address == 0 {
            None
        } else {
            Some(Rsdt::new(VirtAddr::new(self.rsdt_address as u64)))
        }
    }

    /// # Safety
    /// Caller must ensure only one mut ref exists at a time.
    pub unsafe fn rsdt_mut(&mut self) -> Option<ResultStaticErr<&mut Rsdt>> {
        if self.rsdt_address == 0 {
            None
        } else {
            Some(Rsdt::new_mut(VirtAddr::new(self.rsdt_address as u64)))
        }
    }

    pub fn xsdt(&self) -> Option<ResultStaticErr<&Xsdt>> {
        if self.revision < 2 || self.xsdt_address == 0 {
            None
        } else {
            Some(Xsdt::new(VirtAddr::new(self.xsdt_address)))
        }
    }

    /// # Safety
    /// Caller must ensure only one mut ref exists at a time.
    pub unsafe fn xsdt_mut(&mut self) -> Option<ResultStaticErr<&mut Xsdt>> {
        if self.revision < 2 || self.xsdt_address == 0 {
            None
        } else {
            Some(Xsdt::new_mut(VirtAddr::new(self.xsdt_address)))
        }
    }
}

/// Header common for all ACPI tables.
///
/// See Section 5.2.6, System Description Table Header, in the ACPI
/// specification for more details.
#[derive(Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct DescriptionHeader {
    /// ASCII string representation of the table identifer.
    pub signature: [u8; 4],

    /// Length of the table, in bytes, including the header.
    pub length: u32,

    /// Revision of the struture corresponding to the signature field for this
    /// table.
    revision: u8,

    /// The entire table, including the checksum field, must add to zero to be
    /// considered valid.
    checksum: u8,

    /// OEM-supplied string that identifies the OEM.
    oem_id: [u8; 6],

    /// OEM-supplied string that the OEM uses to identify the particular data
    /// table.
    oem_table_id: [u8; 8],

    /// OEM-supplied revision number.
    oem_revision: u32,

    /// Vendor ID of utility that created the table, e.g. the ASL Compiler.
    creator_id: u32,

    /// Revision of the utility that created the table, e.g. revision of the ASL
    /// Compiler.
    creator_revision: u32,
}

impl DescriptionHeader {
    #[allow(dead_code)]
    pub fn signature_as_str(&self) -> &str {
        // Per the ACPI spec, the signature is in ASCII, which is always valid UTF-8.
        core::str::from_utf8(&self.signature)
            .expect("invalid ACPI table signature; not valid UTF-8")
    }

    /// Returns the address range where this table is located.
    pub fn addr_range(&self) -> Range<usize> {
        let base = self as *const _ as usize;
        base..base + self.length as usize
    }

    /// Sets checksum field so that checksum validates.
    /// To be called after modifying any of this structures's data.
    pub fn update_checksum(&mut self) {
        log::info!("Checksum before update: {}, {}", self.checksum, self.compute_checksum());
        self.checksum = self.checksum.wrapping_sub(self.compute_checksum());
        log::info!("Checksum after: {}, {}", self.checksum, self.compute_checksum());
    }

    fn validate(&self) -> ResultStaticErr<()> {
        if self.compute_checksum() != 0 {
            return Err("ACPI table checksum invalid");
        }

        Ok(())
    }

    /// Computes the checksum across all data in this structure.
    fn compute_checksum(&self) -> u8 {
        // Safety: we've ensured that the table is within EBDA.
        let data = unsafe {
            slice::from_raw_parts(self.addr_range().start as *const u8, self.length as usize)
        };
        data.iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs))
    }
}

impl Display for DescriptionHeader {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_fmt(format_args!(
            "Entry {} ({:#x}-{:#x}): {:?}",
            self.signature_as_str(),
            self.addr_range().start,
            self.addr_range().end,
            self
        ))
    }
}

/// Root System Description Table.
///
/// See Section 5.2.7 in the ACPI specification for more details.
#[derive(Debug)]
#[repr(C, align(4))]
pub struct Rsdt {
    pub header: DescriptionHeader,
    // The RSDT contains an array of pointers to other tables, but unfortunately this can't be
    // expressed in Rust. By adding an zero size array here, we can make sure that `entries_arr`
    // always aligns at 4. Otherwise, the compiler will throw an error.
    entries_arr: [u32; 0],
}

pub type RsdtEntryPairMut<'a> = (&'a mut u32, &'a mut DescriptionHeader);

impl Rsdt {
    const SIGNATURE: &'static [u8; 4] = b"RSDT";

    pub fn new(addr: VirtAddr) -> ResultStaticErr<&'static Rsdt> {
        // Safety: we're checking that it's a valid RSDT in `validate()`.
        let rsdt = unsafe { &*addr.as_ptr::<Rsdt>() };
        rsdt.validate()?;
        Ok(rsdt)
    }

    /// # Safety
    /// Caller must ensure only one mut ref exists at a time.
    pub unsafe fn new_mut(addr: VirtAddr) -> ResultStaticErr<&'static mut Rsdt> {
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
    pub fn get(&self, signature: &[u8; 4]) -> ResultStaticErr<Option<&DescriptionHeader>> {
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
    pub fn entry_headers(&self) -> impl Iterator<Item = ResultStaticErr<&DescriptionHeader>> {
        self.entries_arr().iter().map(|&entry| {
            let ptr: *const DescriptionHeader = entry as usize as *const DescriptionHeader;
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
    ) -> ResultStaticErr<Option<RsdtEntryPairMut>> {
        self.validate()?;
        let maybe_found: Option<Result<RsdtEntryPairMut, &str>> =
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

    fn entry_headers_mut(&mut self) -> impl Iterator<Item = ResultStaticErr<RsdtEntryPairMut>> {
        self.entries_arr_mut().iter_mut().map(|addr| {
            let header_ptr = *addr as usize as *mut DescriptionHeader;
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
                (self.header.length as usize - size_of::<DescriptionHeader>()) / size_of::<u32>(),
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
                (self.header.length as usize - size_of::<DescriptionHeader>()) / size_of::<u32>(),
            )
        }
    }

    fn validate(&self) -> ResultStaticErr<()> {
        self.header.validate()?;

        if self.header.signature != *Self::SIGNATURE {
            return Err("Invalid signature for RSDT table");
        }

        if (self.header.length as usize - size_of::<DescriptionHeader>()) % size_of::<u32>() != 0 {
            return Err("RSDT invalid: entries size not a multiple of pointer size");
        }

        Ok(())
    }
}

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

    pub fn new(addr: VirtAddr) -> ResultStaticErr<&'static Xsdt> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let xsdt = unsafe { &*addr.as_ptr::<Xsdt>() };
        xsdt.validate()?;
        Ok(xsdt)
    }

    // # Safety: caller must ensure only one mut ref exists at a time.
    pub fn new_mut(addr: VirtAddr) -> ResultStaticErr<&'static mut Xsdt> {
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
    pub fn get(&self, signature: &[u8; 4]) -> ResultStaticErr<Option<&DescriptionHeader>> {
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
    pub fn entry_ptrs(&self) -> impl Iterator<Item = ResultStaticErr<&XsdtEntryPtr>> {
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
    pub fn get_entry_mut(
        &mut self,
        signature: &[u8; 4],
    ) -> ResultStaticErr<Option<&mut XsdtEntryPtr>> {
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

    fn entries_arr(&self) -> &[XsdtEntryPtr] {
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

    fn entries_arr_mut(&mut self) -> &mut [XsdtEntryPtr] {
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

    fn validate(&self) -> ResultStaticErr<()> {
        self.header.validate()?;

        if self.header.signature != *Self::SIGNATURE {
            return Err("Invalid signature for XSDT table");
        }

        if (self.header.length as usize - size_of::<DescriptionHeader>()) % size_of::<usize>() != 0
        {
            return Err("XSDT invalid: entries size not a multiple of pointer size");
        }

        Ok(())
    }
}

bitflags! {
    #[derive(Clone, Copy, Debug)]
    struct MadtFlags: u32 {
        /// The system also has a PC-AT-compatible dual-8259 setup.
        ///
        /// The 8259 vectors must be disabled (that is, masked) when enabling the ACPI APIC operation.
        const PCAT_COMPAT = 1;
    }

    #[derive(Clone, Copy, Debug)]
    pub struct LocalApicFlags: u32 {
        /// Processor is ready to use.
        const ENABLED = 1;

        /// If disabled, system hardware supports enabling this processor during OS runtime.
        const ONLINE_CAPABLE = 2;
    }
}
/// Multiple APIC Description Table (MADT).
///
/// See Section 5.2.12 in the ACPI specification for more details.
/// Note that the MADT has the same fields as the RSDT plus a few more,
/// the first few fields are the same. These common fields are represented
/// by DescriptionHeader; here we reuse that and add the remaining fields.
/// Table 5.19 of ACPI Spec lists the fields.
#[derive(Debug)]
#[repr(C, packed)]
pub struct Madt {
    pub header: DescriptionHeader,

    /// Physical address of the local APIC for each CPU.
    local_apic_address: u32,

    /// Multiple APIC flags.
    flags: MadtFlags,
    // This is followed by a dynamic number of variable-length interrupt controller structures,
    // which unfortunately can't be expressed in safe Rust. See ControllerHeader below.
}

/// Header for values in MADT field "Interrupt Controller Structure".
/// This is the last field in the MADT and can appear N times, each time
/// containing a different structure (e.g. ProcessorLocalApic) and length
/// according to its type. However, all of these structures look the same in
/// their first 2 fields - we factor them here for reuse and call it a header.
/// We treat this structure in a special way: we use it to parse existing
/// memory and we assume that this is immediately followed by an actual MADT
/// table structure, and it will only `validate` if an instance of this type is
/// in the expected memory region (EBDA). Not meant to be built and passed
/// around.
#[derive(Clone, Copy, Debug, IntoBytes, Immutable)]
#[repr(C, packed)]
pub struct ControllerHeader {
    // There's only 17 possible types, the rest of the range is reserved. We need
    // to use u8 (not enum) as we use this structure to parse existing memory.
    pub structure_type: u8,
    len: u8,
}

impl ControllerHeader {
    fn validate(&self) -> ResultStaticErr<()> {
        Ok(())
    }
}

/// Processor Local Apic Structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. Documented in section 5.2.12.2 of APIC Specification.
#[derive(Debug)]
#[repr(C, packed)]
pub struct ProcessorLocalApic {
    header: ControllerHeader,

    /// Deprecated; maps to a Processor object in the ACPI tree.
    processor_uid: u8,

    /// Processor's local APIC ID.
    pub apic_id: u8,

    /// Local APIC flags.
    pub flags: LocalApicFlags,
}

// Because we cast pointers from *const ControllHeader:
static_assertions::assert_eq_align!(ProcessorLocalApic, ControllerHeader);

impl ProcessorLocalApic {
    pub const STRUCTURE_TYPE: u8 = 0;

    pub fn new(header: &ControllerHeader) -> ResultStaticErr<&Self> {
        if header.structure_type != Self::STRUCTURE_TYPE {
            return Err("structure is not Processor Local APIC Structure");
        }
        header.validate()?;

        // Safety: we're verified that the structure type is correct.
        Ok(unsafe { &*(header as *const _ as usize as *const Self) })
    }
}

/// Processor Local x2APIC structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. Documented in section 5.2.12.12 of APIC Specification.
#[derive(Debug)]
#[repr(C, packed)]
pub struct ProcessorLocalX2Apic {
    header: ControllerHeader,

    /// Reserverd, must be zero.
    _reserved: u16,

    /// The processor's local X2APIC ID.
    pub x2apic_id: u32,

    /// Local APIC flags.
    pub flags: LocalApicFlags,

    /// OSPM associates the X2APIC Structure with a processor object declared in
    /// the namespace using the Device statement, when the _UID child object
    /// of the processor device evaluates to a numeric value, by matching
    /// the numeric value with this field.
    processor_uid: u32,
}

// Because we cast pointers from *const ControllHeader:
static_assertions::assert_eq_align!(ProcessorLocalX2Apic, ControllerHeader);

impl ProcessorLocalX2Apic {
    pub const STRUCTURE_TYPE: u8 = 9;

    pub fn new(header: &ControllerHeader) -> ResultStaticErr<&Self> {
        if header.structure_type != Self::STRUCTURE_TYPE {
            return Err("structure is not Processor Local X2APIC Structure");
        }
        header.validate()?;

        // Safety: we're verified that the structure type is correct.
        Ok(unsafe { &*(header as *const _ as usize as *const Self) })
    }
}

/// Multiprocessor Wakeup structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. Documented in section 5.2.12.19 of APIC Specification.
#[derive(Debug, IntoBytes, Immutable)]
#[repr(C, packed)]
pub struct MultiprocessorWakeup {
    /// Interrupt structure common header.
    /// Type must be 0x10, length must be 16.
    header: ControllerHeader,

    /// MailBox version: must be set to 0.
    mailbox_version: u16,

    /// 4 bytes reserved.
    _reserved: [u8; 4],

    /// Physical address of the mailbox. It must be in ACPINvs. It must also be
    /// 4K bytes aligned. Memory declared in stage0_bin/layout.ld. Mailbox
    /// structure defined in table 5.44 of ACPI Spec.
    pub mailbox_address: u64,
}

// Because we cast pointers from *const ControllHeader:
static_assertions::assert_eq_align!(MultiprocessorWakeup, ControllerHeader);

impl MultiprocessorWakeup {
    pub const STRUCTURE_TYPE: u8 = 0x10;
    const MULTIPROCESSOR_WAKEUP_STRUCTURE_LENGTH: u8 = 16;

    /// Gets a reference to a MultiprocessorWakeup given a reference to its
    /// first field (header). This assumes that the memory that immediately
    /// follows header is actually a MultiprocessorWakeup.
    pub fn from_header_cast(header: &ControllerHeader) -> ResultStaticErr<&Self> {
        Self::check_header(header)?;

        let header_raw_pointer = header as *const _ as *const Self;
        // Deref to get a &Self. Safety: we're verified correct structure type.
        // There's no guarantee the actual structure comforms to that type.
        Ok(unsafe { &*(header_raw_pointer) })
    }

    pub fn from_header_mut(header: &mut ControllerHeader) -> ResultStaticErr<&mut Self> {
        Self::check_header(header)?;

        // # Safety: we have validated the structure.
        Ok(unsafe { (header as *mut _ as *mut Self).as_mut().unwrap() })
    }

    fn check_header(header: &ControllerHeader) -> ResultStaticErr<()> {
        if header.structure_type != Self::STRUCTURE_TYPE {
            return Err("structure is not MultiprocessorWakeup");
        }
        if header.len != Self::MULTIPROCESSOR_WAKEUP_STRUCTURE_LENGTH {
            return Err("MultiprocessorWakeup structure length must be 16");
        }
        header.validate()
    }
}

impl Default for MultiprocessorWakeup {
    fn default() -> Self {
        MultiprocessorWakeup {
            header: ControllerHeader {
                structure_type: MultiprocessorWakeup::STRUCTURE_TYPE,
                len: MultiprocessorWakeup::MULTIPROCESSOR_WAKEUP_STRUCTURE_LENGTH,
            },
            mailbox_version: 0,
            _reserved: [0; 4],
            mailbox_address: 0,
        }
    }
}

impl Madt {
    pub const SIGNATURE: &'static [u8; 4] = b"APIC";

    pub fn new(hdr: &DescriptionHeader) -> ResultStaticErr<&'static Madt> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let madt = unsafe { &*(hdr as *const _ as usize as *const Madt) };
        madt.validate()?;
        Ok(madt)
    }

    /// Interprets buf as a Madt, validates it, then sets the length
    /// of the resulting Madt to match that of the given buffer.
    pub fn from_buf_mut(buf: &mut [u8]) -> ResultStaticErr<&mut Madt> {
        if buf.len() < size_of::<Madt>() {
            return Err("Buffer too small for MADT");
        }
        let madt_ptr = buf.as_mut_ptr() as *mut Self;
        check_ptr_aligned(madt_ptr);
        // # Safety: we have checked for overrun and we're checking it's a valid MADT
        // with `validate()`.
        let madt = unsafe { &mut *madt_ptr };

        madt.validate()?;

        // Set header length to buf length for consistency. Caller can adjust.
        madt.header.length = buf.len() as u32;
        madt.header.update_checksum();

        Ok(madt)
    }

    pub fn from_header_mut(hdr: &mut DescriptionHeader) -> ResultStaticErr<&'static mut Madt> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let madt =
            unsafe {
                (hdr as *mut _ as *mut Madt).as_mut().unwrap() // Pointer obtained from a ref can't be null.
            };
        madt.validate()?;
        Ok(madt)
    }

    pub fn as_byte_slice(&self) -> ResultStaticErr<&'static [u8]> {
        self.validate()?;
        // Safety: we have just checked that the MADT is entirely in the EBDA.
        Ok(unsafe {
            slice::from_raw_parts(self as *const _ as *const u8, self.header.length as usize)
        })
    }

    fn validate(&self) -> ResultStaticErr<()> {
        self.header.validate()?;

        if self.header.signature != *Self::SIGNATURE {
            return Err("Invalid signature for MADT table");
        }

        Ok(())
    }

    /// Create an iterator over entries of field Interrupt Controller Structure
    /// that returns references to the entries' headers.
    pub fn controller_struct_headers(&self) -> MadtIterator<'_> {
        // The Madt struct does not itself contain the interrupt controller
        // entries (see struct Madt above) but these entries are expected to
        // exist right after the Madt struct. Therefore, we set the offset to
        // point to one byte after, which is size_of Madt.
        MadtIterator { madt: self, offset: size_of::<Madt>() }
    }

    /// If a MultiprocessorWakeupStructure exsists in this MADT, updates its
    /// mailbox_address. Otherwise, relocates this MADT to somewhere free in
    /// EBDA and appends to it a new MultiprocessorWakeupStructure with the
    /// given os_mailbox_address. Returns a ref to the maybe relocated MADT.
    pub fn set_or_append_mp_wakeup(
        &mut self,
        os_mailbox_address: u64,
    ) -> ResultStaticErr<&mut Self> {
        if let Some(prexisting_mpw_header) =
            self.get_controller_structure_mut(MultiprocessorWakeup::STRUCTURE_TYPE)
        {
            log::info!("A MultiprocessorWakeup structure already exists in MADT, updating.");
            // # Safety: We are not using `prexisting_mpw_header` after this call.
            let prexisting_mpw = MultiprocessorWakeup::from_header_mut(prexisting_mpw_header)?;
            prexisting_mpw.mailbox_address = os_mailbox_address;
            self.header.update_checksum();
            return Ok(self);
        }

        log::info!("Relocating MADT and appending a new MultiprocessorWakeup to it.");

        let old_madt_len = self.header.length as usize;
        let new_madt_len =
            old_madt_len + MultiprocessorWakeup::MULTIPROCESSOR_WAKEUP_STRUCTURE_LENGTH as usize;

        // New contents = old contents + MPW. Allocate new length, copy old contents.
        let mut new_madt_buf = Vec::with_capacity_in(new_madt_len, &HIGH_MEMORY_ALLOCATOR);
        new_madt_buf.extend_from_slice(self.as_byte_slice()?);
        log::info!("MADT contents copied to {:?}", new_madt_buf.as_ptr_range());

        // Make an MPW somwhere then copy over its bytes after old MADT contents.
        let temp_mpw: MultiprocessorWakeup =
            MultiprocessorWakeup { mailbox_address: os_mailbox_address, ..Default::default() };
        new_madt_buf.extend_from_slice(temp_mpw.as_bytes());
        log::info!(
            "Written Multiprocessor Wakeup Structure to: {:?}",
            new_madt_buf[old_madt_len..new_madt_len].as_ptr_range()
        );

        let new_madt = Madt::from_buf_mut(new_madt_buf.leak())
            .map_err(|_| "MADT no longer valid after adding MultiprocessorWakeup")?;
        log::info!("New MADT loaded, at {:#x}", new_madt as *const _ as usize);
        Ok(new_madt)
    }

    fn get_controller_structure_mut(
        &mut self,
        structure_type: u8,
    ) -> Option<&mut ControllerHeader> {
        self.get_controller_structure(structure_type).map(
            // Safety: we hold a mut ref to self, only one mut ref to a header can be held at time.
            // We have already checked control_header is a valid reference.
            |maybe_found| unsafe {
                (maybe_found as *const _ as *mut ControllerHeader).as_mut().unwrap()
            },
        )
    }

    /// Seeks a structure with the given type in this MADT's Interrupt Controlle
    /// Structure fields and returns a reference to its header if found.
    fn get_controller_structure(&self, structure_type: u8) -> Option<&ControllerHeader> {
        self.controller_struct_headers()
            .find(|control_header| control_header.structure_type == structure_type)
    }
}

pub struct MadtIterator<'a> {
    madt: &'a Madt,

    /// Offset with respect to where Madt starts where the first interrupt
    /// controller entry starts. The first interrupt controller entry
    /// should be right after the Madt struct ends, and its address should be
    /// address of Madt (madt, above) + length of madt (offset)
    offset: usize,
}

impl<'a> Iterator for MadtIterator<'a> {
    type Item = &'a ControllerHeader;

    fn next(&mut self) -> Option<Self::Item> {
        if self.offset + size_of::<ControllerHeader>() > self.madt.header.length as usize {
            // we'd overflow the MADT structure; nothing more to read
            return None;
        }
        // Safety: now we know that at least reading the header won't overflow the data
        // structure.
        let header = unsafe {
            let header_ptr =
                (self.madt as *const _ as *const u8).add(self.offset) as *const ControllerHeader;
            check_ptr_aligned(header_ptr);
            &*header_ptr
        };
        if self.offset + header.len as usize > self.madt.header.length as usize {
            // returning this header would overflow MADT
            return None;
        }

        // If the MADT has some zeroed space at the end, then we'll land somewhere that
        // reports a 0-length header. The following clause prevents falling in
        // an infinite loop in that case.
        if header.len == 0 {
            return None; // Prevent infinite interation.
        }

        self.offset += header.len as usize;
        Some(header)
    }
}

fn check_ptr_aligned<T>(ptr: *const T) {
    if !ptr.is_aligned() {
        panic!("Incorrect pointer {:?} alignmnt for type {}", ptr, type_name::<T>());
    }
}
