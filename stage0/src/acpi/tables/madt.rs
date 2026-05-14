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

use alloc::{alloc::Allocator, boxed::Box, vec::Vec};
use core::fmt::Debug;

use bitflags::bitflags;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout, TryFromBytes};

use crate::{
    AcpiTable, DescriptionHeader,
    acpi::{
        HIGH_MEMORY_ALLOCATOR,
        tables::{Checksum, Result, signature},
    },
};

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C)]
pub struct Signature(signature::A, signature::P, signature::I, signature::C);
static_assertions::assert_eq_size!(DescriptionHeader<Signature>, [u8; 36usize]);

impl From<Signature> for [u8; 4] {
    fn from(signature: Signature) -> [u8; 4] {
        [signature.0 as u8, signature.1 as u8, signature.2 as u8, signature.3 as u8]
    }
}

#[derive(Clone, Copy, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
pub struct MadtFlags(u32);

#[derive(Clone, Copy, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
pub struct LocalApicFlags(u32);

bitflags! {
    impl MadtFlags: u32 {
        /// The system also has a PC-AT-compatible dual-8259 setup.
        ///
        /// The 8259 vectors must be disabled (that is, masked) when enabling the ACPI APIC operation.
        const PCAT_COMPAT = 1;
    }

    impl LocalApicFlags: u32 {
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
#[derive(IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct Madt {
    pub header: DescriptionHeader<Signature>,

    /// Physical address of the local APIC for each CPU.
    local_apic_address: u32,

    /// Multiple APIC flags.
    flags: MadtFlags,

    // This is followed by a dynamic number of variable-length interrupt controller structures,
    // which unfortunately can't be expressed in safe Rust. See ControllerHeader below.
    data: [u8],
}

impl Debug for Madt {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let local_apic_address = self.local_apic_address;
        let flags = self.flags;
        f.debug_struct("Madt")
            .field("header", &self.header)
            .field("local_apic_address", &local_apic_address)
            .field("flags", &flags)
            .finish_non_exhaustive()
    }
}

impl Checksum for Madt {
    fn checksum(&self) -> u8 {
        self.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs))
    }
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
#[derive(Copy, Clone, Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C, packed)]
pub struct ControllerHeader<T> {
    // There's only 17 possible types, the rest of the range is reserved. We need
    // to use u8 (not enum) as we use this structure to parse existing memory.
    pub structure_type: T,
    len: u8,
}

#[derive(Copy, Clone, Debug, Default, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum ProcessorLocalApicType {
    #[default]
    ProcessorLocalApic = 0,
}
/// Processor Local Apic Structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. Documented in section 5.2.12.2 of APIC Specification.
#[derive(Debug, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct ProcessorLocalApic {
    header: ControllerHeader<ProcessorLocalApicType>,

    /// Deprecated; maps to a Processor object in the ACPI tree.
    processor_uid: u8,

    /// Processor's local APIC ID.
    pub apic_id: u8,

    /// Local APIC flags.
    pub flags: LocalApicFlags,
}
static_assertions::assert_eq_size!(ProcessorLocalApic, [u8; 8]);

#[derive(Copy, Clone, Debug, Default, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum ProcessorLocalX2ApicType {
    #[default]
    ProcessorLocalX2Apic = 9,
}
/// Processor Local x2APIC structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. Documented in section 5.2.12.12 of APIC Specification.
#[derive(Debug, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct ProcessorLocalX2Apic {
    header: ControllerHeader<ProcessorLocalX2ApicType>,

    /// Reserved, must be zero.
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
static_assertions::assert_eq_size!(ProcessorLocalX2Apic, [u8; 16]);

#[derive(Copy, Clone, Debug, Default, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum MultiprocessorWakeupType {
    #[default]
    MultiprocessorWakeup = 0x10,
}

/// Multiprocessor Wakeup structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. Documented in section 5.2.12.19 of APIC Specification.
#[derive(Debug, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct MultiprocessorWakeup {
    header: ControllerHeader<MultiprocessorWakeupType>,

    /// MailBox version: must be set to 0.
    mailbox_version: u16,

    /// 4 bytes reserved.
    _reserved: [u8; 4],

    /// Physical address of the mailbox. It must be in ACPINvs. It must also be
    /// 4K bytes aligned. Memory declared in stage0_bin/layout.ld. Mailbox
    /// structure defined in table 5.44 of ACPI Spec.
    pub mailbox_address: u64,
}
static_assertions::assert_eq_size!(MultiprocessorWakeup, [u8; 16usize]);

impl Default for MultiprocessorWakeup {
    fn default() -> Self {
        MultiprocessorWakeup {
            header: ControllerHeader {
                structure_type: MultiprocessorWakeupType::default(),
                len: size_of::<MultiprocessorWakeup>() as u8,
            },
            mailbox_version: 0,
            _reserved: [0; 4],
            mailbox_address: 0,
        }
    }
}

impl AcpiTable for Madt {
    type Signature = Signature;

    fn try_from_bytes(buf: &[u8]) -> Result<(&Self, &[u8])> {
        // As `Madt` is `?Sized`, we can't just do `size_of()` here. The basic MADT size
        // is the size of the header + the two `u32` fields.
        // Hopefully there is a better way to do this.
        const MADT_SIZE: usize = size_of::<DescriptionHeader<Signature>>() + 4 + 4;
        // First, try to parse the header.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid MADT header")?;
        log::info!("got MADT header");
        // if it parses, it is a MADT, and we can get a length from there
        if (header.length as usize) < MADT_SIZE {
            return Err("invalid MADT");
        }
        let entries = header.length as usize - MADT_SIZE;

        let (madt, tail) =
            Madt::try_ref_from_prefix_with_elems(buf, entries).map_err(|_| "invalid MADT")?;

        madt.validate()?;

        Ok((madt, tail))
    }

    fn try_from_bytes_mut(buf: &mut [u8]) -> Result<(&mut Self, &mut [u8])> {
        // First, try to parse the header.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid MADT header")?;
        // if it parses, it is a MADT, and we can get a length from there
        if (header.length as usize) < size_of::<DescriptionHeader<Signature>>() + 4 + 4 {
            return Err("invalid MADT");
        }
        let entries = header.length as usize - (size_of::<DescriptionHeader<Signature>>() + 4 + 4);

        let (madt, tail) =
            Madt::try_mut_from_prefix_with_elems(buf, entries).map_err(|_| "invalid MADT")?;

        madt.validate()?;

        Ok((madt, tail))
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Self::Signature> {
        &mut self.header
    }
}

impl Madt {
    pub fn new_with_size<A: Allocator>(num: usize, alloc: A) -> Box<Self> {
        let mut header = DescriptionHeader::<Signature> {
            signature: Signature::default(),
            length: (size_of::<DescriptionHeader<Signature>>() + 8 + num) as u32,
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

        let mut buf = Vec::with_capacity_in(header.length as usize, alloc);
        buf.resize(header.length as usize, 0);

        header.write_to_prefix(&mut buf[..]).unwrap();

        let buf = Vec::leak(buf);
        // This `unwrap()` and assertion should never fail.
        let (madt, suffix) = Self::try_from_bytes_mut(buf.as_mut_bytes()).unwrap();
        assert!(suffix.is_empty());

        // Safety: the memory was leaked from a Box; the pointer does not change, and
        // the size does not change.
        unsafe { Box::from_raw(madt) }
    }

    /// Create an iterator over entries of field Interrupt Controller Structure
    /// that returns references to the entries.
    pub fn iter(&self) -> MadtIterator<'_> {
        MadtIterator { data: &self.data }
    }

    pub fn iter_mut(&mut self) -> MadtIterMut<'_> {
        MadtIterMut { data: &mut self.data }
    }

    /// If a MultiprocessorWakeupStructure exsists in this MADT, updates its
    /// mailbox_address. Otherwise, relocates this MADT to somewhere free in
    /// EBDA and appends to it a new MultiprocessorWakeupStructure with the
    /// given os_mailbox_address. Returns a ref to the maybe relocated MADT.
    pub fn set_or_append_mp_wakeup(&mut self, os_mailbox_address: u64) -> Result<&mut Self> {
        self.set_or_append_mp_wakeup_in(os_mailbox_address, &HIGH_MEMORY_ALLOCATOR)
    }

    pub fn set_or_append_mp_wakeup_in<A: Allocator>(
        &mut self,
        os_mailbox_address: u64,
        alloc: A,
    ) -> Result<&mut Self> {
        if let Some(preexisting_mpw) =
            self.get_controller_structure_mut(MultiprocessorWakeupType::default() as u8)
        {
            log::info!("A MultiprocessorWakeup structure already exists in MADT, updating.");

            let preexisting_mpw =
                MultiprocessorWakeup::try_mut_from_bytes(preexisting_mpw.as_mut_bytes())
                    .map_err(|_| "invalid MultiprocessorWakeup in MADT")?;
            preexisting_mpw.mailbox_address = os_mailbox_address;
            self.update_checksum();
            return Ok(self);
        }

        log::info!("Relocating MADT and appending a new MultiprocessorWakeup to it.");

        let old_madt_len = self.header.length;
        let new_madt_len = old_madt_len + size_of::<MultiprocessorWakeup>() as u32;

        // New contents = old contents + MPW. Allocate new length, copy old contents.
        let mut new_madt =
            Madt::new_with_size(self.data.len() + size_of::<MultiprocessorWakeup>(), alloc);
        new_madt.header = self.header;
        new_madt.header.length = new_madt_len;
        new_madt.flags = self.flags;
        new_madt.local_apic_address = self.local_apic_address;
        new_madt.data[..self.data.len()].copy_from_slice(&self.data);

        log::info!("MADT contents copied to {:?}", new_madt.as_bytes().as_ptr_range());

        // Make an MPW somwhere then copy over its bytes after old MADT contents.
        let temp_mpw: MultiprocessorWakeup =
            MultiprocessorWakeup { mailbox_address: os_mailbox_address, ..Default::default() };
        new_madt.data[self.data.len()..].copy_from_slice(temp_mpw.as_bytes());
        log::info!(
            "Written Multiprocessor Wakeup Structure to: {:?}",
            new_madt.data[self.data.len()..].as_ptr_range()
        );

        new_madt.update_checksum();
        log::info!("New MADT loaded, at {:p}", new_madt.as_bytes().as_ptr());
        Ok(Box::leak(new_madt))
    }

    fn get_controller_structure_mut(
        &mut self,
        structure_type: u8,
    ) -> Option<&mut ControllerStructure> {
        self.iter_mut().find(|structure| structure.header.structure_type == structure_type)
    }

    #[cfg(test)]
    fn get_controller_structure(&self, structure_type: u8) -> Option<&ControllerStructure> {
        self.iter().find(|structure| structure.header.structure_type == structure_type)
    }
}

/// Generic representation of a MADT entry.
#[derive(Immutable, IntoBytes, KnownLayout, FromBytes)]
#[repr(C, packed)]
pub struct ControllerStructure {
    pub header: ControllerHeader<u8>,
    data: [u8],
}

pub struct MadtIterator<'a> {
    data: &'a [u8],
}

impl<'a> Iterator for MadtIterator<'a> {
    type Item = &'a ControllerStructure;

    fn next(&mut self) -> Option<Self::Item> {
        let len = {
            let header = ControllerHeader::<u8>::try_ref_from_bytes(
                self.data.get(..core::mem::size_of::<ControllerHeader<u8>>())?,
            )
            .ok()?;
            header.len as usize
        };

        // If the MADT has some zeroed space at the end, then we'll land somewhere that
        // reports a 0-length header. The following clause prevents falling in
        // an infinite loop in that case.
        if len == 0 {
            return None; // Prevent infinite interation.
        }

        let data = core::mem::take(&mut self.data);
        let (item_data, rest) = data.split_at_checked(len)?;
        self.data = rest;

        ControllerStructure::ref_from_bytes(item_data).ok()
    }
}

pub struct MadtIterMut<'a> {
    data: &'a mut [u8],
}

impl<'a> Iterator for MadtIterMut<'a> {
    type Item = &'a mut ControllerStructure;

    fn next(&mut self) -> Option<Self::Item> {
        let len = {
            let header = ControllerHeader::<u8>::try_ref_from_bytes(
                self.data.get(..core::mem::size_of::<ControllerHeader<u8>>())?,
            )
            .ok()?;
            header.len as usize
        };

        // If the MADT has some zeroed space at the end, then we'll land somewhere that
        // reports a 0-length header. The following clause prevents falling in
        // an infinite loop in that case.
        if len == 0 {
            return None; // Prevent infinite interation.
        }

        let data = core::mem::take(&mut self.data);
        let (item_data, rest) = data.split_at_mut_checked(len)?;
        self.data = rest;

        ControllerStructure::mut_from_bytes(item_data).ok()
    }
}

#[derive(Copy, Clone, Debug, Default, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum IoApicType {
    #[default]
    IoApic = 1,
}
/// I/O Apic Structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. There is at at least one or more IO APIC in an APIC implementation.
/// Documented in section 5.2.12.3 of APIC Specification.
#[derive(Debug, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct IoApic {
    header: ControllerHeader<IoApicType>,

    /// Processor's local APIC ID.
    pub io_apic_id: u8,

    /// Should be set to zero
    _reserved: u8,

    /// 32-bit addr for this APIC. Each I/O APIC resides at a unique address.
    io_apic_addr: u32,

    /// Global interrupt number where the interrupt inputs start at
    global_system_interrupt_base: u32,
}
static_assertions::assert_eq_size!(IoApic, [u8; 12usize]);

#[derive(Copy, Clone, Debug, Default, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum InterruptSourceOverrideType {
    #[default]
    InterruptSourceOverride = 2,
}
/// Interrupt Source Override structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. It describes variances between the IA-PC standard dual 8259 and
/// the actual platform implementation.
///
/// Documented in section 5.2.12.5 of APIC Specification.
#[derive(Debug, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct InterruptSourceOverride {
    header: ControllerHeader<InterruptSourceOverrideType>,

    /// Should be set to zero for ISA
    bus: u8,

    /// Bus-relative interrupt source (Interrupt request)
    source: u8,

    /// Will signal this global system interrupt
    global_system_interrupt: u32,

    /// See documentation for the various bits set.
    flags: u16,
}
static_assertions::assert_eq_size!(InterruptSourceOverride, [u8; 10usize]);

#[derive(Copy, Clone, Debug, Default, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum LocalApicNmiType {
    #[default]
    LocalApicNmiType = 4,
}
/// Local APIC NMI (Non-Maskable Interrupt) structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. If provided, describes the Local APIC interrupt input for a
/// processor. It's needed by Linux to enable an appropriate APIC entry.
///
/// Documented in section 5.2.12.7 of APIC Specification.
#[derive(Debug, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct LocalApicNmi {
    header: ControllerHeader<LocalApicNmiType>,

    /// Deprecated; maps to a Processor object in the ACPI tree.
    processor_uid: u8,

    /// See documentation for the various bits set.
    flags: u16,

    /// Describe which local interrupt number is connected to NMI
    local_apic_lint_num: u8,
}
static_assertions::assert_eq_size!(LocalApicNmi, [u8; 6usize]);

#[cfg(test)]
mod tests {
    use googletest::prelude::*;

    use super::*;

    // This MADT is obtained from a machine running on GCP.
    const MADT: &[u8] = &[
        0x41, 0x50, 0x49, 0x43, 0x76, 0x00, 0x00, 0x00, 0x05, 0x22, 0x47, 0x6f, 0x6f, 0x67, 0x6c,
        0x65, 0x47, 0x4f, 0x4f, 0x47, 0x41, 0x50, 0x49, 0x43, 0x01, 0x00, 0x00, 0x00, 0x47, 0x4f,
        0x4f, 0x47, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe0, 0xfe, 0x01, 0x00, 0x00, 0x00, 0x00,
        0x08, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x08, 0x01, 0x01, 0x01, 0x00, 0x00, 0x00,
        0x01, 0x0c, 0x00, 0x00, 0x00, 0x00, 0xc0, 0xfe, 0x00, 0x00, 0x00, 0x00, 0x02, 0x0a, 0x00,
        0x05, 0x05, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x02, 0x0a, 0x00, 0x09, 0x09, 0x00, 0x00, 0x00,
        0x0d, 0x00, 0x02, 0x0a, 0x00, 0x0a, 0x0a, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x02, 0x0a, 0x00,
        0x0b, 0x0b, 0x00, 0x00, 0x00, 0x0d, 0x00, 0x04, 0x06, 0xff, 0x00, 0x00, 0x01,
    ];

    #[test]
    fn test_parse_madt() {
        let (madt, _) = Madt::try_from_bytes(MADT).unwrap();
        assert_that!(&madt.header.oem_id, eq(b"Google"));
        assert_that!(&madt.header.oem_table_id, eq(b"GOOGAPIC"));
    }

    #[test]
    fn test_madt_iter() {
        let (madt, _) = Madt::try_from_bytes(MADT).unwrap();
        assert_that!(
            madt.iter().map(|entry| entry.header.structure_type).collect::<Vec<u8>>(),
            unordered_elements_are![&0, &0, &1, &2, &2, &2, &2, &4]
        )
    }

    #[test]
    fn test_madt_iter_mut() {
        let mut madt_buf = MADT.to_vec();
        let (madt, _) = Madt::try_from_bytes_mut(&mut madt_buf).unwrap();
        for entry in madt.iter_mut() {
            entry.header.structure_type = 0xFF;
        }
        assert_that!(
            madt.iter().map(|entry| entry.header.structure_type).collect::<Vec<u8>>(),
            unordered_elements_are![&0xFF, &0xFF, &0xFF, &0xFF, &0xFF, &0xFF, &0xFF, &0xFF]
        )
    }

    const LAPIC: &[u8] = &[0x00, 0x08, 0x01, 0x02, 0x03, 0x00, 0x00, 0x00];
    const LX2APIC: &[u8] = &[
        0x09, 0x10, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, //
        0x03, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x00,
    ];

    #[test]
    fn test_lapic() {
        let generic = ControllerStructure::try_ref_from_bytes(LAPIC).unwrap();
        assert_that!(generic.header.structure_type, eq(0));
        assert_that!(generic.header.len, eq(LAPIC.len() as u8));
        assert_that!(generic.data.len(), eq(6));
        assert_that!(
            ProcessorLocalApic::try_ref_from_bytes(generic.as_bytes()),
            ok(points_to(matches_pattern!(ProcessorLocalApic {
                processor_uid: &1,
                apic_id: &2,
                ..
            })))
        );

        // completely wrong data structure
        assert_that!(ProcessorLocalApic::try_ref_from_bytes(LX2APIC), err(anything()));

        // extra junk at the end
        let mut invalid_lapic = LAPIC.to_vec();
        invalid_lapic.push(0x00);
        assert_that!(ProcessorLocalApic::try_ref_from_bytes(&invalid_lapic[..]), err(anything()));
    }

    #[test]
    fn test_x2apic() {
        let generic = ControllerStructure::try_ref_from_bytes(LX2APIC).unwrap();
        assert_that!(generic.header.structure_type, eq(9));
        assert_that!(generic.header.len, eq(LX2APIC.len() as u8));
        assert_that!(generic.data.len(), eq(14));
        assert_that!(ProcessorLocalX2Apic::try_ref_from_bytes(generic.as_bytes()), ok(anything()));
    }

    #[test]
    fn test_add_mp_wakeup() {
        let (old_madt, _) = Madt::try_from_bytes(MADT).unwrap();

        let mut madt_buf = MADT.to_vec();
        let (madt, _) = Madt::try_from_bytes_mut(&mut madt_buf).unwrap();

        let new_madt = madt.set_or_append_mp_wakeup_in(0x01020304, std::alloc::Global).unwrap();
        assert_that!(
            new_madt.header.length,
            eq(old_madt.header.length + size_of::<MultiprocessorWakeup>() as u32)
        );

        // Spot-check that the fields that we expect to stay the same are indeed the
        // same.
        assert_that!(new_madt.header.oem_id, eq(&old_madt.header.oem_id[..]));
        assert_that!(new_madt.header.revision, eq(old_madt.header.revision));
        assert_that!(new_madt.local_apic_address, eq(old_madt.local_apic_address));

        // Strictly speaking, we're only interested that new_madt.data is contained
        // within new_madt.data, but there is no convenient way to check that.
        assert!(new_madt.data.starts_with(&old_madt.data));

        let mp_wakeup = new_madt
            .get_controller_structure(MultiprocessorWakeupType::default() as u8)
            .map(|entry| MultiprocessorWakeup::try_ref_from_bytes(entry.as_bytes()))
            .unwrap()
            .unwrap();
        let mailbox = mp_wakeup.mailbox_address;
        assert_that!(mailbox, eq(0x01020304));

        let new_madt_ptr = new_madt.as_bytes().as_ptr();
        let new_madt_v2 =
            new_madt.set_or_append_mp_wakeup_in(0x04030201, std::alloc::Global).unwrap();

        // This change should have been made in-place.
        assert_that!(new_madt_v2.as_bytes().as_ptr(), eq(new_madt_ptr));

        let mp_wakeup = new_madt_v2
            .get_controller_structure(MultiprocessorWakeupType::default() as u8)
            .map(|entry| MultiprocessorWakeup::try_ref_from_bytes(entry.as_bytes()))
            .unwrap()
            .unwrap();
        let mailbox = mp_wakeup.mailbox_address;
        assert_that!(mailbox, eq(0x04030201));
    }
}
