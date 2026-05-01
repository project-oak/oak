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

use alloc::vec::Vec;
use core::slice;

use bitflags::bitflags;
use zerocopy::{Immutable, IntoBytes};

use crate::{
    DescriptionHeader,
    acpi::{
        HIGH_MEMORY_ALLOCATOR,
        tables::{Result, check_ptr_aligned},
    },
};

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
    pub header: DescriptionHeader<[u8; 4]>,

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
    fn validate(&self) -> Result<()> {
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

    pub fn new(header: &ControllerHeader) -> Result<&Self> {
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

    pub fn new(header: &ControllerHeader) -> Result<&Self> {
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
    pub fn from_header_cast(header: &ControllerHeader) -> Result<&Self> {
        Self::check_header(header)?;

        let header_raw_pointer = header as *const _ as *const Self;
        // Deref to get a &Self. Safety: we're verified correct structure type.
        // There's no guarantee the actual structure comforms to that type.
        Ok(unsafe { &*(header_raw_pointer) })
    }

    pub fn from_header_mut(header: &mut ControllerHeader) -> Result<&mut Self> {
        Self::check_header(header)?;

        // # Safety: we have validated the structure.
        Ok(unsafe { (header as *mut _ as *mut Self).as_mut().unwrap() })
    }

    fn check_header(header: &ControllerHeader) -> Result<()> {
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

    pub fn new(hdr: &DescriptionHeader<[u8; 4]>) -> Result<&'static Madt> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let madt = unsafe { &*(hdr as *const _ as usize as *const Madt) };
        madt.validate()?;
        Ok(madt)
    }

    /// Interprets buf as a Madt, validates it, then sets the length
    /// of the resulting Madt to match that of the given buffer.
    pub fn from_buf_mut(buf: &mut [u8]) -> Result<&mut Madt> {
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

    pub fn from_header_mut(hdr: &mut DescriptionHeader<[u8; 4]>) -> Result<&'static mut Madt> {
        // Safety: we're checking that it's a valid XSDT in `validate()`.
        let madt = unsafe {
            (hdr as *mut _ as *mut Madt).as_mut().unwrap() // Pointer obtained from a ref can't be null.
        };
        madt.validate()?;
        Ok(madt)
    }

    pub fn as_byte_slice(&self) -> Result<&'static [u8]> {
        self.validate()?;
        // Safety: we have just checked that the MADT is entirely in the EBDA.
        Ok(unsafe {
            slice::from_raw_parts(self as *const _ as *const u8, self.header.length as usize)
        })
    }

    fn validate(&self) -> Result<()> {
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
    pub fn set_or_append_mp_wakeup(&mut self, os_mailbox_address: u64) -> Result<&mut Self> {
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

/// I/O Apic Structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. There is at at least one or more IO APIC in an APIC implementation.
/// Documented in section 5.2.12.3 of APIC Specification.
#[derive(Debug)]
#[repr(C, packed)]
pub struct IoApic {
    header: ControllerHeader,

    /// Processor's local APIC ID.
    pub io_apic_id: u8,

    /// Should be set to zero
    _reserved: u8,

    /// 32-bit addr for this APIC. Each I/O APIC resides at a unique address.
    io_apic_addr: u32,

    /// Global interrupt number where the interrupt inputs start at
    global_system_interrupt_base: u32,
}

// Because we cast pointers from *const ControllHeader:
static_assertions::assert_eq_align!(IoApic, ControllerHeader);
static_assertions::assert_eq_size!(IoApic, [u8; 12usize]);

impl IoApic {
    pub const STRUCTURE_TYPE: u8 = 1;
    // Explicitly stated in the spec
    pub const EXPECTED_LENGTH: u8 = 12;

    pub fn new(header: &ControllerHeader) -> Result<&Self> {
        if header.structure_type != Self::STRUCTURE_TYPE {
            return Err("structure is not an I/O APIC Structure");
        }
        header.validate()?;

        if header.len != Self::EXPECTED_LENGTH {
            log::error!(
                "IO APIC struct expected length of {}, got {}",
                Self::EXPECTED_LENGTH,
                header.len
            );
            return Err("IO APIC length is expected to be 12");
        }

        // Safety: we're verified that the structure type is correct.
        let io_apic = unsafe { &*(header as *const _ as usize as *const Self) };
        io_apic.validate()?;
        Ok(io_apic)
    }

    fn validate(&self) -> Result<()> {
        if self.header.len != Self::EXPECTED_LENGTH {
            log::error!(
                "IO APIC struct expected length of {}, got {}",
                Self::EXPECTED_LENGTH,
                self.header.len
            );
            return Err("IO APIC length is expected to be 12");
        }
        Ok(())
    }
}

/// Interrupt Source Override structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. It describes variances between the IA-PC standard dual 8259 and
/// the actual platform implementation.
///
/// Documented in section 5.2.12.5 of APIC Specification.
#[derive(Debug)]
#[repr(C, packed)]
pub struct InterruptSourceOverride {
    header: ControllerHeader,

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

impl InterruptSourceOverride {
    pub const STRUCTURE_TYPE: u8 = 2;
    // Explicitly stated in the spec
    pub const EXPECTED_LENGTH: u8 = 10;

    pub fn new(header: &ControllerHeader) -> Result<&Self> {
        if header.structure_type != Self::STRUCTURE_TYPE {
            return Err("structure is not Interrupt Source Override Structure");
        }
        header.validate()?;

        // Safety: we're verified that the structure type is correct.
        let interrupt_source_override = unsafe { &*(header as *const _ as usize as *const Self) };
        interrupt_source_override.validate()?;
        Ok(interrupt_source_override)
    }

    fn validate(&self) -> Result<()> {
        if self.header.len != Self::EXPECTED_LENGTH {
            log::error!(
                "Interrupt source override struct expected length of {}, got {}",
                Self::EXPECTED_LENGTH,
                self.header.len
            );
            return Err("Interrupt Source Override length is expected to be 10");
        }

        if self.bus != 0 {
            // Stated in spec as 0 (constant) for ISA
            return Err("Interrupt Source Override bus was not set to 0 for ISA");
        }
        Ok(())
    }
}

/// Local APIC NMI (Non-Maskable Interrupt) structure.
/// One of the possible structures in MADT's Interrupt Controller Structure
/// field. If provided, describes the Local APIC interrupt input for a
/// processor. It's needed by Linux to enable an appropriate APIC entry.
///
/// Documented in section 5.2.12.7 of APIC Specification.
#[derive(Debug)]
#[repr(C, packed)]
pub struct LocalApicNmi {
    header: ControllerHeader,

    /// Deprecated; maps to a Processor object in the ACPI tree.
    processor_uid: u8,

    /// See documentation for the various bits set.
    flags: u16,

    /// Describe which local interrupt number is connected to NMI
    local_apic_lint_num: u8,
}

static_assertions::assert_eq_size!(LocalApicNmi, [u8; 6usize]);

impl LocalApicNmi {
    pub const STRUCTURE_TYPE: u8 = 4;
    // Explicitly stated in the spec
    pub const EXPECTED_LENGTH: u8 = 6;

    pub fn new(header: &ControllerHeader) -> Result<&Self> {
        if header.structure_type != Self::STRUCTURE_TYPE {
            return Err("structure is not LocalApicNmi");
        }
        header.validate()?;

        // Safety: we're verified that the structure type is correct.
        let local_apic_nmi = unsafe { &*(header as *const _ as usize as *const Self) };
        local_apic_nmi.validate()?;
        Ok(local_apic_nmi)
    }

    fn validate(&self) -> Result<()> {
        if self.header.len != Self::EXPECTED_LENGTH {
            log::error!(
                "Local APIC NMI struct expected length of {}, got {}",
                Self::EXPECTED_LENGTH,
                self.header.len
            );
            return Err("Local APIC NMI length is expected to be 6");
        }
        Ok(())
    }
}
