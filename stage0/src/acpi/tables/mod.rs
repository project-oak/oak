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

//! Defines ACPI structures based on ACPI specification.
//! You can find this specification here:
//! https://uefi.org/htmlspecs/ACPI_Spec_6_4_html/05_ACPI_Software_Programming_Model/ACPI_Software_Programming_Model.html
//!
//! ACPI tables are located in the first 1KB of the EBDA (Extended Bios Data
//! Area) or in the BIOS read-only memory space between 0E0000h and 0FFFFFh. The
//! basic structure of ACPI tables is as follows:
//!
//! - RSDP (Root System Descriptor Pointer) is a structure (not a pointer)
//!   described in ACPI Spec section 5.2.5. Its location is hardcoded by the
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
//!     substructures described below.
//!
//!     - RSDT and XSDT entry pointers point to a number of possible
//!       substructures, each with a 4-byte signature, listed in tables 5.5 and
//!       5.6 of ACPI Spec.
//!     - One such substructure is a MADT (Multiple APIC Description Table),
//!       with signature "APIC", described in ACPI Spec section 5.2.12. A MADT
//!       (our type: `Madt`) contains a header (also a `DescriptionHeader`), a
//!       couple more fields, plus a variable number of variable length
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

mod fadt;
pub mod madt;
mod rsdp;
pub mod rsdt;
mod xsdt;

use core::{any::type_name, fmt::Display, ops::Range, slice};

pub use fadt::Fadt;
pub use madt::Madt;
pub use rsdp::Rsdp;
pub use rsdt::Rsdt;
pub use xsdt::Xsdt;

type Result<T> = core::result::Result<T, &'static str>;

/// "Alphabet" to construct various ACPI table signatures.
#[allow(dead_code)]
pub mod signature {
    use zerocopy::{Immutable, IntoBytes, KnownLayout, TryFromBytes};

    #[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum D {
        D = b'D',
    }

    #[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum P {
        P = b'P',
    }

    #[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum R {
        R = b'R',
    }

    #[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum S {
        S = b'S',
    }

    #[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum T {
        T = b'T',
    }

    #[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum Space {
        Space = b' ',
    }
}

/// Header common for all ACPI tables.
///
/// See Section 5.2.6, System Description Table Header, in the ACPI
/// specification for more details.
#[derive(Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct DescriptionHeader<S> {
    /// ASCII string representation of the table identifer.
    pub(super) signature: S,

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

impl DescriptionHeader<[u8; 4]> {
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

    pub fn validate(&self) -> Result<()> {
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

impl Display for DescriptionHeader<[u8; 4]> {
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

pub fn check_ptr_aligned<T>(ptr: *const T) {
    if !ptr.is_aligned() {
        panic!("Incorrect pointer {:?} alignmnt for type {}", ptr, type_name::<T>());
    }
}
