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

use alloc::vec::Vec;
use core::{any::type_name, default::Default, fmt::Display, ops::Range, slice};

pub use fadt::Fadt;
pub use madt::Madt;
pub use rsdp::Rsdp;
pub use rsdt::Rsdt;
use x86_64::VirtAddr;
pub use xsdt::Xsdt;
use zerocopy::{Immutable, IntoBytes, KnownLayout, TryFromBytes};

type Result<T> = core::result::Result<T, &'static str>;

/// "Alphabet" to construct various ACPI table signatures.
#[allow(dead_code)]
pub mod signature {
    use zerocopy::{Immutable, IntoBytes, KnownLayout, TryFromBytes};

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum A {
        #[default]
        A = b'A',
    }

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum C {
        #[default]
        C = b'C',
    }

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum D {
        #[default]
        D = b'D',
    }

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum F {
        #[default]
        F = b'F',
    }

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum P {
        #[default]
        P = b'P',
    }

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum R {
        #[default]
        R = b'R',
    }

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum S {
        #[default]
        S = b'S',
    }

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum T {
        #[default]
        T = b'T',
    }

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum X {
        #[default]
        X = b'X',
    }

    #[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
    #[repr(u8)]
    pub enum Space {
        #[default]
        Space = b' ',
    }
}

/// Header common for all ACPI tables.
///
/// See Section 5.2.6, System Description Table Header, in the ACPI
/// specification for more details.
#[derive(Clone, Copy, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
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
}

impl<S> DescriptionHeader<S> {
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
            //extern crate std;
            //std::eprintln!("checksum {}", self.compute_checksum());
            return Err("ACPI table checksum invalid");
        }

        Ok(())
    }

    /// Computes the checksum across all data in this structure.
    fn compute_checksum(&self) -> u8 {
        // SECURITY: `self.length` may be untrusted. Validate it falls
        // within our ACPI memory. Returning non-zero fails the checksum.
        let self_addr = self as *const _ as usize;
        let length = self.length as usize;
        if !crate::acpi::acpi_memory_contains(self_addr, length) {
            return 1;
        }
        // Safety: we just validated that `[self_addr, self_addr + length)`
        // lies inside an ACPI memory region.
        let data = unsafe { slice::from_raw_parts(self_addr as *const u8, length) };
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

pub trait Checksum {
    fn checksum(&self) -> u8;
}

// If the data structure can be interpreted as bytes, we can provide a default
// implementation.
impl<T: IntoBytes + Immutable> Checksum for T {
    fn checksum(&self) -> u8 {
        self.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs))
    }
}

/// An ACPI System Description Table, as per Section 5.2 of the ACPI
/// specification.
pub trait AcpiTable: Checksum {
    /// Signature of the ACPI table. Must be four bytes.
    type Signature: Default;

    fn try_from_bytes(buf: &[u8]) -> Result<(&Self, &[u8])>;
    fn try_from_bytes_mut(buf: &mut [u8]) -> Result<(&mut Self, &mut [u8])>;

    fn header_mut(&mut self) -> &mut DescriptionHeader<Self::Signature>;

    fn validate(&self) -> Result<()> {
        if self.checksum() != 0 {
            return Err("ACPI table checksum invalid");
        }

        Ok(())
    }

    fn update_checksum(&mut self) {
        let checksum = self.header_mut().checksum.wrapping_sub(self.checksum());
        self.header_mut().checksum = checksum;
    }
}

/// A generic holder for ACPI tables and the byte where we expect to find them.
///
/// Instead of deferencing pointers, accessing ACPI tables can be done safely
/// through this struct as we check that any pointers are pointing to somewhere
/// in the buffers (and ensure there is no overlap between data structures), or
/// we fail.
pub struct AcpiTables<'a> {
    buffers: Vec<&'a mut [u8]>,

    pub rsdp: &'a mut dyn Rsdp,
    rsdt: Option<&'a mut Rsdt>,
    xsdt: Option<&'a mut Xsdt>,
}

impl<'a> AcpiTables<'a> {
    pub fn new(mut buffers: Vec<&'a mut [u8]>, rsdp_addr: VirtAddr) -> Result<Self> {
        let rsdp = buffers
            .extract_if(.., |s| VirtAddr::from_ptr(*s) == rsdp_addr)
            .next()
            .ok_or("RSDP not found")?;
        let rsdp = <dyn Rsdp>::try_from_bytes_mut(rsdp)?;

        Ok(Self { buffers, rsdp, rsdt: None, xsdt: None })
    }

    /// Returns a reference to the RSDT table, if it exists.
    pub fn rsdt(&mut self) -> Result<Option<&mut Rsdt>> {
        if self.rsdt.is_none() {
            let rsdt_ptr = self.rsdp.rsdt().ok_or("RSDT pointer not in RSDP")?;
            let buf = self.find_buf(rsdt_ptr).ok_or("invalid RSDT pointer in RSDP")?;

            let (rsdt, suffix) = Rsdt::try_from_bytes_mut(buf)?;
            if !suffix.is_empty() {
                self.buffers.push(suffix);
            }
            self.rsdt = Some(rsdt)
        }

        Ok(self.rsdt.as_deref_mut())
    }

    /// Returns a reference to the XSDT table, if it exists.
    pub fn xsdt(&mut self) -> Result<Option<&mut Xsdt>> {
        if self.xsdt.is_none() {
            if self.rsdp.xsdt().is_none() {
                return Ok(None);
            }

            let xsdt_ptr = self.rsdp.xsdt().unwrap();
            let buf = self.find_buf(xsdt_ptr).ok_or("invalid XSDT pointer in RSDP")?;

            let (xsdt, suffix) = Xsdt::try_from_bytes_mut(buf)?;
            if !suffix.is_empty() {
                self.buffers.push(suffix);
            }
            self.xsdt = Some(xsdt)
        }

        Ok(self.xsdt.as_deref_mut())
    }

    pub fn try_parse_table_at<T: AcpiTable + ?Sized>(&self, addr: VirtAddr) -> Option<&T> {
        for buffer in &self.buffers {
            if VirtAddr::from_ptr(*buffer) <= addr
                && VirtAddr::from_ptr(*buffer) + (buffer.len() as u64) > addr
            {
                let buffer = &buffer[addr.as_u64() as usize - (buffer.as_ptr() as usize)..];
                let (table, _) = T::try_from_bytes(buffer).ok()?;
                return Some(table);
            }
        }

        None
    }

    pub fn try_parse_header_at<S: TryFromBytes + Immutable>(
        &self,
        addr: VirtAddr,
    ) -> Option<&DescriptionHeader<S>> {
        for buffer in &self.buffers {
            if VirtAddr::from_ptr(*buffer) <= addr
                && VirtAddr::from_ptr(*buffer) + (buffer.len() as u64) > addr
            {
                let buffer = &buffer[addr.as_u64() as usize - (buffer.as_ptr() as usize)..];
                let (header, _) = DescriptionHeader::<S>::try_ref_from_prefix(buffer).ok()?;
                return Some(header);
            }
        }

        None
    }

    /// Tries to find a buffer that contains the address in the buffers list.
    ///
    /// You can think of the matcher buffer being "prefix-struct-suffix", where
    /// prefix is any number of bytes before the `addr` (may be zero), struct is
    /// the arbitrary number of bytes needed to parse a data structure, and
    /// suffix are the bytes left over (if any).
    ///
    /// This function pushes the prefix bytes (if any) back to the buffers list;
    /// as we don't know what the size of the struct is, the caller needs to
    /// push the suffix bytes (if any) back onto the buffers list.
    fn find_buf(&mut self, addr: VirtAddr) -> Option<&'a mut [u8]> {
        let buf = self
            .buffers
            .extract_if(.., |s| {
                VirtAddr::from_ptr(*s) <= addr && VirtAddr::from_ptr(*s) + (s.len() as u64) > addr
            })
            .next()?;
        let (prefix, buf) =
            buf.split_at_mut_checked(addr.as_u64() as usize - (buf.as_ptr() as usize))?;
        if !prefix.is_empty() {
            self.buffers.push(prefix);
        }
        Some(buf)
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;
    use libc;

    use super::*;
    use crate::acpi::tables::rsdp::Rsdp2;

    #[test]
    pub fn test_rsdt() {
        let mut rsdt = Rsdt::new_with_size(1);
        rsdt.entries[0] = 0x12345678;
        rsdt.update_checksum();
        let rsdt = rsdt.as_bytes().to_vec();

        // This bypasses the normal allocation methods completely as we need to
        // guarantee that the RSDT lands somewhere in the 32-bit address space. This
        // can't be guaranteed using the normal Rust mechanics, so we need to use the
        // underlying libc code to mmap us a chunk of memory with a 32-bit pointer.
        let rsdt = {
            // Safety: mmap allocates us a new chunk of anonymous memory that was previously
            // unused.
            let raw_ptr = unsafe {
                libc::mmap(
                    std::ptr::null_mut(),
                    rsdt.len(),
                    libc::PROT_READ | libc::PROT_WRITE,
                    libc::MAP_SHARED | libc::MAP_ANONYMOUS | libc::MAP_32BIT,
                    0,
                    0,
                )
            };
            assert!(!raw_ptr.is_null());
            // Safety: the mmap allocation succeeded, and the length is at least
            // `rsdt.len()`.
            let slice = unsafe { std::slice::from_raw_parts_mut(raw_ptr as *mut u8, rsdt.len()) };
            slice.copy_from_slice(&rsdt);
            slice
        };

        let rsdp = Rsdp2::new(VirtAddr::from_ptr(rsdt)).unwrap().as_bytes().to_vec().leak();

        let rsdp_addr = VirtAddr::from_ptr(rsdp);
        let mut tables = AcpiTables::new(vec![rsdt, rsdp], rsdp_addr).unwrap();

        let test_rsdt = tables.rsdt().unwrap().unwrap();

        assert_that!(test_rsdt.entries, unordered_elements_are!(eq(&0x12345678)));

        // Note: we leak the `rsdt` here, but it should be okay as this is just
        // a test.
    }
}
