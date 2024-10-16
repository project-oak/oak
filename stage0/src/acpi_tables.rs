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

/// Defines ACPI structures based on ACPI specification.
/// You can find this specification here:
/// https://uefi.org/htmlspecs/ACPI_Spec_6_4_html/05_ACPI_Software_Programming_Model/ACPI_Software_Programming_Model.html
use core::{marker::PhantomData, mem::size_of, ops::Deref, slice};

use bitflags::bitflags;
use x86_64::VirtAddr;
use zerocopy::{AsBytes, FromBytes, FromZeroes};

use crate::acpi::{EBDA, EBDA_SIZE};

/// ACPI Root System Description Pointer.
///
/// Used to locate either the RSDT or XSDT in memory.
///
/// See Section 5.2.5 in the ACPI specification, Version 6.5 for more details.
#[derive(FromZeroes, FromBytes, AsBytes)]
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
    rsdt_address: u32,

    // ACPI 2.0 fields.
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

impl Rsdp {
    pub fn validate(&self) -> Result<(), &'static str> {
        if &self.signature != b"RSD PTR " {
            return Err("Invalid RSDP signature");
        }
        let len = if self.revision > 2 { self.length } else { 20 } as usize;

        if len > size_of::<Rsdp>() {
            return Err("invalid RSDP size");
        }

        let checksum = self.as_bytes()[..20].iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));

        if checksum != 0 {
            return Err("Invalid RSDP checksum");
        }

        if self.revision > 2 {
            let checksum = self.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));

            if checksum != 0 {
                return Err("Invalid RSDP extended checksum");
            }
        }

        // Check the pointer addresses; if they are valid, they should point within the
        // EBDA. Safety: we will never dereference the pointer, we just need to
        // know where it points to.
        let ebda_base = unsafe { EBDA.as_ptr() } as usize;
        if self.rsdt_address > 0
            && ((self.rsdt_address as usize) < ebda_base
                || (self.rsdt_address as usize) >= ebda_base + EBDA_SIZE)
        {
            return Err("Invalid RSDT address: does not point to within EBDA");
        }
        if self.xsdt_address > 0
            && ((self.xsdt_address as usize) < ebda_base
                || (self.xsdt_address as usize) >= ebda_base + EBDA_SIZE)
        {
            return Err("Invalid XSDT address: does not point to within EBDA");
        }

        Ok(())
    }

    pub fn rsdt(&self) -> Result<Option<&Rsdt>, &'static str> {
        if self.rsdt_address == 0 {
            Ok(None)
        } else {
            Rsdt::new(VirtAddr::new(self.rsdt_address as u64)).map(Some)
        }
    }

    pub fn xsdt(&self) -> Result<Option<&Xsdt>, &'static str> {
        if self.xsdt_address == 0 {
            Ok(None)
        } else {
            Xsdt::new(VirtAddr::new(self.xsdt_address)).map(Some)
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
    signature: [u8; 4],

    /// Length of the table, in bytes, including the header.
    length: u32,

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
    pub fn signature(&self) -> &str {
        // Per the ACPI spec, the signature is in ASCII, which is always valid UTF-8.
        core::str::from_utf8(&self.signature)
            .expect("invalid ACPI table signature; not valid UTF-8")
    }

    fn validate(&self) -> Result<(), &'static str> {
        // Safety: we're never dereferencing this pointer.
        let ebda_base = unsafe { EBDA.as_ptr() } as usize;
        let ebda = ebda_base..ebda_base + EBDA_SIZE;
        let table = {
            let base = self as *const _ as usize;
            base..base + self.length as usize
        };

        if !ebda.contains(&table.start) || !ebda.contains(&table.end) {
            return Err("ACPI table falls outside EBDA");
        }

        // Safety: we've ensured that the table is within EBDA.
        let data = unsafe { slice::from_raw_parts(table.start as *const u8, self.length as usize) };
        let checksum = data.iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));
        if checksum != 0 {
            return Err("ACPI table checksum invalid");
        }

        Ok(())
    }
}

/// Root System Description Table.
///
/// See Section 5.2.7 in the ACPI specification for more details.
#[repr(C, packed)]
pub struct Rsdt {
    header: DescriptionHeader,
    // The RSDT contains an array of pointers to other tables, but unfortunately this can't be
    // expressed in Rust.
}

impl Rsdt {
    const SIGNATURE: &'static [u8; 4] = b"RSDT";

    pub fn new(addr: VirtAddr) -> Result<&'static Rsdt, &'static str> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let rsdt = unsafe { &*addr.as_ptr::<Rsdt>() };
        rsdt.validate()?;
        Ok(rsdt)
    }

    fn validate(&self) -> Result<(), &'static str> {
        self.header.validate()?;

        if self.header.signature != *Self::SIGNATURE {
            return Err("Invalid signature for RSDT table");
        }

        if (self.header.length as usize - size_of::<DescriptionHeader>()) % size_of::<u32>() != 0 {
            return Err("RSDT invalid: entries size not a multiple of pointer size");
        }

        // Safety: we're never dereferencing the pointer.
        let ebda_base = unsafe { EBDA.as_ptr() } as usize;
        for &entry in self.entries() {
            let ptr: usize = entry as usize;
            if !(ebda_base..ebda_base + EBDA_SIZE).contains(&ptr) {
                return Err("RSDT invalid: entry points outside EBDA");
            }
        }
        Ok(())
    }

    fn entries(&self) -> &[u32] {
        let entries_base = self as *const _ as usize + size_of::<DescriptionHeader>();
        // Safety: we've validated that the address and length makes sense in
        // `validate()`.
        unsafe {
            slice::from_raw_parts(
                entries_base as *const u32,
                (self.header.length as usize - size_of::<DescriptionHeader>()) / size_of::<u32>(),
            )
        }
    }

    /// Finds a table based on the signature, if it is present.
    pub fn get(&self, table: &[u8; 4]) -> Option<&'static DescriptionHeader> {
        self.entries().iter().find_map(|&entry| {
            let ptr = entry as usize;
            let entry: &'static DescriptionHeader = unsafe { &*(ptr as *const DescriptionHeader) };
            if entry.signature == *table {
                Some(entry)
            } else {
                None
            }
        })
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

impl<'a> XsdtEntryPtr<'a> {
    pub fn raw_val(&self) -> u64 {
        // As per Section 5.2 in the ACPI specification 6.5,
        // Address is little endian.
        u64::from_le_bytes(self.addr)
    }
}

impl<'a> Deref for XsdtEntryPtr<'a> {
    type Target = DescriptionHeader;

    fn deref(&self) -> &DescriptionHeader {
        // Safety: the address has been validated in Xsdt::validate().
        unsafe { &*(self.raw_val() as *const DescriptionHeader) }
    }
}

/// Extended System Description Table.
///
/// See Section 5.2.8 in the ACPI specification for more details.
#[repr(C, packed)]
pub struct Xsdt {
    header: DescriptionHeader,
    // The XSDT contains an array of pointers to other tables, but unfortunately this can't be
    // expressed in Rust.
}

impl Xsdt {
    const SIGNATURE: &'static [u8; 4] = b"XSDT";

    pub fn new(addr: VirtAddr) -> Result<&'static Xsdt, &'static str> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let xsdt = unsafe { &*addr.as_ptr::<Xsdt>() };
        xsdt.validate()?;
        Ok(xsdt)
    }

    fn validate(&self) -> Result<(), &'static str> {
        self.header.validate()?;

        if self.header.signature != *Self::SIGNATURE {
            return Err("Invalid signature for XSDT table");
        }

        if (self.header.length as usize - size_of::<DescriptionHeader>()) % size_of::<usize>() != 0
        {
            return Err("XSDT invalid: entries size not a multiple of pointer size");
        }

        // Safety: we're never dereferencing the pointer.
        let ebda_base = unsafe { EBDA.as_ptr() } as usize;
        for entry in self.entries() {
            let ptr = entry.raw_val() as usize;
            if !(ebda_base..ebda_base + EBDA_SIZE).contains(&ptr) {
                return Err("XSDT invalid: entry points outside EBDA");
            }
        }
        Ok(())
    }

    pub fn entries(&self) -> &[XsdtEntryPtr] {
        let entries_base = self as *const _ as usize + size_of::<DescriptionHeader>();
        // Safety: we've validated that the address and length makes sense in
        // `validate()`. XsdtEntryPtr is 1-byte aligned.
        unsafe {
            slice::from_raw_parts(
                entries_base as *const XsdtEntryPtr,
                (self.header.length as usize - size_of::<DescriptionHeader>())
                    / size_of::<XsdtEntryPtr>(),
            )
        }
    }

    /// Finds a table based on the signature, if it is present.
    pub fn get(&self, table: &[u8; 4]) -> Option<&DescriptionHeader> {
        self.entries().iter().find(|entry| entry.signature == *table).map(|p| &**p)
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
    header: DescriptionHeader,

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
#[derive(Clone, Copy, Debug)]
#[repr(C, packed)]
pub(crate) struct ControllerHeader {
    // There's only 17 possible types, the rest of the range is reserved. We need
    // to use u8 (not enum) as we use this structure to parse existing memory.
    pub structure_type: u8,
    len: u8,
}

impl ControllerHeader {
    fn validate(&self) -> Result<(), &'static str> {
        // Safety: we're never dereferencing this pointer.
        let ebda_base = unsafe { EBDA.as_ptr() } as usize;
        let ebda = ebda_base..ebda_base + EBDA_SIZE;
        let structure = {
            let base = self as *const _ as usize;
            base..base + self.len as usize
        };

        if !ebda.contains(&structure.start) || !ebda.contains(&structure.end) {
            return Err("ACPI interrupt data structure falls outside EBDA");
        }

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

impl ProcessorLocalApic {
    pub const STRUCTURE_TYPE: u8 = 0;

    pub fn new(header: &ControllerHeader) -> Result<&Self, &'static str> {
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

impl ProcessorLocalX2Apic {
    pub const STRUCTURE_TYPE: u8 = 9;

    pub fn new(header: &ControllerHeader) -> Result<&Self, &'static str> {
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
#[derive(Debug)]
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
    pub mailbox_address: u8,
}

impl MultiprocessorWakeup {
    pub const STRUCTURE_TYPE: u8 = 0x10;
    const MULTIPROCESSOR_WAKEUP_STRUCTURE_LENGTH: u8 = 16;

    /// Gets a reference to a MultiprocessorWakeup given a reference to its
    /// first field (header). This assumes that the memory that immediately
    /// follows header is actually a MultiprocessorWakeup.
    pub fn from_header_cast(header: &ControllerHeader) -> Result<&Self, &'static str> {
        if header.structure_type != Self::STRUCTURE_TYPE {
            return Err("structure is not MultiprocessorWakeup");
        }
        if header.len != Self::MULTIPROCESSOR_WAKEUP_STRUCTURE_LENGTH {
            return Err("MultiprocessorWakeup structure length must be 16");
        }
        header.validate()?;

        let header_raw_pointer = header as *const _ as *const Self;
        // Deref to get a &Self. Safety: we're verified correct structure type.
        // There's no guarantee the actual structure comforms to that type.
        Ok(unsafe { &*(header_raw_pointer) })
    }
}

impl Madt {
    pub const SIGNATURE: &'static [u8; 4] = b"APIC";

    pub fn new(hdr: &DescriptionHeader) -> Result<&'static Madt, &'static str> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let madt = unsafe { &*(hdr as *const _ as usize as *const Madt) };
        madt.validate()?;
        Ok(madt)
    }

    fn validate(&self) -> Result<(), &'static str> {
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
}

pub(crate) struct MadtIterator<'a> {
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
            &*((self.madt as *const _ as *const u8).add(self.offset) as *const ControllerHeader)
        };
        if self.offset + header.len as usize > self.madt.header.length as usize {
            // returning this header would overflow MADT
            return None;
        }

        self.offset += header.len as usize;
        Some(header)
    }
}
