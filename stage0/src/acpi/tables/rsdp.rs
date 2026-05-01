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

use alloc::boxed::Box;
use core::fmt::Debug;

use x86_64::VirtAddr;
use zerocopy::{Immutable, IntoBytes, KnownLayout, TryFromBytes};

use crate::acpi::tables::{Result, Xsdt, signature};

pub trait Rsdp: Debug {
    fn validate(&self) -> Result<()>;

    fn rsdt(&self) -> Option<VirtAddr>;
    fn xsdt(&self) -> Option<VirtAddr>;

    /// # Safety
    /// Caller must guarantee the RSDT pointer is valid..
    unsafe fn xsdt_ref(&self) -> Option<Result<&Xsdt>> {
        Some(Xsdt::new(self.xsdt()?))
    }

    /// # Safety
    /// Caller must guarantee the RSDT pointer is valid.
    /// Caller must ensure only one mut ref exists at a time.
    unsafe fn xsdt_mut(&mut self) -> Option<Result<&mut Xsdt>> {
        Some(unsafe { Xsdt::new_mut(self.xsdt()?) })
    }
}

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum RsdpAcpi1Version {
    V1 = 0,
}

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(u8)]
enum RsdpAcpi2Version {
    #[default]
    V2 = 2,
}

// "RSD PTR " signature.
// This uses the trick from zerocopy example, where it makes use of
// single-element enums to ensure there is exactly one way how to represent the
// signature.
#[allow(dead_code)]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C)]
pub struct RsdpSignature(
    signature::R,
    signature::S,
    signature::D,
    signature::Space,
    signature::P,
    signature::T,
    signature::R,
    signature::Space,
);

/// ACPI Root System Description Pointer, Version 1.
///
/// Used to locate the RSDT in memory.
///
/// See Section 5.2.5.3 in the ACPI specification, Version 6.6 for more details.
#[repr(C, packed)]
#[derive(Debug, Copy, Clone, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
struct Rsdp1 {
    /// Signature: "RSD PTR " (note the trailing space).
    signature: RsdpSignature,

    /// Checksum for fields defined in the ACPI 1.0 specification.
    checksum: u8,

    /// OEM-supplied identification string.
    oemid: [u8; 6],

    /// Revision of this structure.
    ///
    /// ACPI 1.0 value is zero, ACPI 2.0 value is 2.
    revision: RsdpAcpi1Version,

    /// 32-bit physical address of the RSDT.
    rsdt_address: u32,
}
static_assertions::assert_eq_size!(Rsdp1, [u8; 20usize]);

impl Rsdp for Rsdp1 {
    fn validate(&self) -> Result<()> {
        let checksum = self.as_bytes()[..20].iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));

        if checksum != 0 {
            return Err("Invalid RSDP checksum");
        }
        Ok(())
    }

    fn rsdt(&self) -> Option<VirtAddr> {
        if self.rsdt_address == 0 { None } else { Some(VirtAddr::new(self.rsdt_address as u64)) }
    }

    fn xsdt(&self) -> Option<VirtAddr> {
        None
    }
}

/// ACPI Root System Description Pointer, Version 2.
///
/// Used to locate either the RSDT or XSDT in memory.
///
/// See Section 5.2.5.3 in the ACPI specification, Version 6.6 for more details.
#[repr(C, packed)]
#[derive(Debug, IntoBytes, Immutable, KnownLayout, TryFromBytes)]
pub struct Rsdp2 {
    /// Signature: "RSD PTR " (note the trailing space).
    signature: RsdpSignature,

    /// Checksum for fields defined in the ACPI 1.0 specification.
    checksum: u8,

    /// OEM-supplied identification string.
    oemid: [u8; 6],

    /// Revision of this structure.
    ///
    /// ACPI 1.0 value is zero, ACPI 2.0 value is 2.
    revision: RsdpAcpi2Version,

    /// 32-bit physical address of the RSDT.
    rsdt_address: u32,

    /// Length of the table, including the header.
    length: u32,

    /// 64-bit physical address of the XSDT.
    xsdt_address: u64,

    /// Checksum of the entire table, including both checksum fields.
    extended_checksum: u8,

    /// Reserved
    _reserved: [u8; 3],
}
static_assertions::assert_eq_size!(Rsdp2, [u8; 36usize]);

impl Rsdp2 {
    #[allow(unused)]
    fn checksum(&self) -> u8 {
        // Just the RSDP1 header.
        self.as_bytes()[..size_of::<Rsdp1>()].iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs))
    }

    #[allow(unused)]
    fn extended_checksum(&self) -> u8 {
        self.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs))
    }

    #[allow(unused)]
    pub fn new(rsdt: VirtAddr) -> Result<Box<Self>> {
        let mut rsdp = Box::new(Self {
            signature: RsdpSignature::default(),
            checksum: 0,
            oemid: [0; 6],
            revision: RsdpAcpi2Version::default(),
            rsdt_address: rsdt
                .as_u64()
                .try_into()
                .map_err(|_| "RSDT address not in low 32 bits")?,
            length: size_of::<Rsdp2>() as u32,
            xsdt_address: 0,
            extended_checksum: 0,
            _reserved: [0; 3],
        });
        rsdp.checksum = rsdp.checksum.wrapping_sub(rsdp.checksum());
        rsdp.extended_checksum = rsdp.extended_checksum.wrapping_sub(rsdp.extended_checksum());

        Ok(rsdp)
    }
}

impl Rsdp for Rsdp2 {
    fn validate(&self) -> Result<()> {
        let checksum = self.as_bytes().iter().fold(0u8, |lhs, &rhs| lhs.wrapping_add(rhs));

        if checksum != 0 {
            return Err("Invalid RSDP checksum");
        }

        Ok(())
    }

    fn rsdt(&self) -> Option<VirtAddr> {
        if self.rsdt_address == 0 { None } else { Some(VirtAddr::new(self.rsdt_address as u64)) }
    }

    fn xsdt(&self) -> Option<VirtAddr> {
        if self.xsdt_address == 0 { None } else { Some(VirtAddr::new(self.xsdt_address)) }
    }
}

impl dyn Rsdp {
    pub fn try_from_bytes_mut(buf: &mut [u8]) -> Result<&mut dyn Rsdp> {
        // Try as ACPI 2.0 first.
        let rsdp = match Rsdp2::try_mut_from_prefix(buf) {
            Ok((rsdp, _)) => rsdp as &mut dyn Rsdp,
            Err(err) => {
                let (rsdp, _) =
                    Rsdp1::try_mut_from_prefix(err.into_src()).map_err(|_| "invalid RSDP")?;
                rsdp as &mut dyn Rsdp
            }
        };

        rsdp.validate()?;

        Ok(rsdp)
    }
}

#[cfg(test)]
mod tests {
    use std::vec::Vec;

    use googletest::prelude::*;

    use super::*;

    #[test]
    pub fn test_parse_valid_rsdp1() {
        let mut buf = Vec::from(b"RSD PTR \x57 TEST \x00\x01\x02\x03\x04");
        assert_that!(<dyn Rsdp>::try_from_bytes_mut(&mut buf[..]), ok(anything()));
    }

    #[test]
    pub fn test_parse_valid_rsdp2() {
        let mut buf = Vec::from(b"RSD PTR \x55 TEST \x02\x01\x02\x03\x04\0\0\0\0\x01\x02\x03\x04\x05\x06\x07\x08\xDC\x00\x00\x00");
        assert_that!(<dyn Rsdp>::try_from_bytes_mut(&mut buf[..]), ok(anything()));
    }

    #[test]
    pub fn test_invalid_rsdp_checksum() {
        let mut buf = Vec::from(b"RSD PTR \x55 TEST \x00\x01\x02\x03\x04");
        assert_that!(<dyn Rsdp>::try_from_bytes_mut(&mut buf[..]), err(anything()));

        let mut buf = Vec::from(b"RSD PTR \x55 TEST \x02\x01\x02\x03\x04\0\0\0\0\x01\x02\x03\x04\x05\x06\x07\x08\xCC\x00\x00\x00");
        assert_that!(<dyn Rsdp>::try_from_bytes_mut(&mut buf[..]), err(anything()));
    }

    #[test]
    pub fn test_empty() {
        let mut buf = Vec::from(b"");
        assert_that!(<dyn Rsdp>::try_from_bytes_mut(&mut buf[..]), err(anything()));
    }

    #[test]
    pub fn test_wrong_version() {
        let mut buf = Vec::from(b"RSD PTR \x55 TEST \x00\x02\x02\x03\x04");
        assert_that!(<dyn Rsdp>::try_from_bytes_mut(&mut buf[..]), err(anything()));
    }

    #[test]
    pub fn test_garbage() {
        let mut buf = Vec::from(b"\x01\x02\x03\x04\x05\x06\x07\x08\x55 TEST \x00\x02\x02\x03\x04");
        assert_that!(<dyn Rsdp>::try_from_bytes_mut(&mut buf[..]), err(anything()));
    }

    #[test]
    pub fn test_new_parse() {
        let rsdp = Rsdp2::new(VirtAddr::new(0x1000)).unwrap();
        assert_that!(rsdp.rsdt(), some(eq(VirtAddr::new(0x1000))));
        assert_that!(rsdp.xsdt(), none());

        let mut buf = rsdp.as_bytes().to_vec();
        let rsdp2 = <dyn Rsdp>::try_from_bytes_mut(&mut buf[..]).unwrap();
        assert_that!(rsdp2.rsdt(), eq(rsdp.rsdt()));
        assert_that!(rsdp2.xsdt(), eq(rsdp.xsdt()));
    }
}
