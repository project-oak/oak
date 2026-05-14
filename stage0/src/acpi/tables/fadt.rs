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

use core::fmt::Debug;

use zerocopy::{Immutable, IntoBytes, KnownLayout, TryFromBytes};

use crate::{
    DescriptionHeader,
    acpi::tables::{AcpiTable, Checksum, Result, signature},
};

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C)]
pub struct Signature(signature::F, signature::A, signature::C, signature::P);
static_assertions::assert_eq_size!(DescriptionHeader<Signature>, [u8; 36usize]);

// GAS for short. This is a structure used to describe the position of
// registers.
// See section 5.2.3.2 in the ACPI specification for more details.
#[derive(Copy, Clone, Debug, Default, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct GenericAddressStructure {
    address_space: u8,
    bit_width: u8,
    bit_offset: u8,
    access_size: u8,
    address: u64,
}
static_assertions::assert_eq_size!(GenericAddressStructure, [u8; 12usize]);

/// Fixed ACPI Description Table (FADT) for ACPI 2.0.
///
/// The QEMU `q35` machines have this version.
#[derive(Clone, Debug, Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct FadtAcpi2 {
    // The Revision field must be "2".."4" (the ACPI major version, with the minor version in
    // `fadt_minor_version`.
    pub header: DescriptionHeader<Signature>,

    // The remaining fields are a complex list of components describing
    // fixed hardware information
    pub firmware_ctrl: u32,
    pub dsdt_address: u32,

    // Reserved bits. Populated in ACPI 1.0, but removed in ACPI 2.0. Remains for compatibility
    // only
    _reserved1: u8,

    preferred_power_management_profile: u8,
    sci_interrupt: u16,
    sci_command_port_address: u32,
    acpi_enable: u8,
    acpi_disable: u8,
    s4bios_req: u8,
    pstate_control: u8,

    // Addresses for system ports
    pm1a_event_block: u32, // required field
    pm1b_event_block: u32,
    pm1a_control_block: u32, // required field
    pm1b_control_block: u32,
    pm2_control_block: u32,
    pm_timer_block: u32,
    general_purpose_event0_block: u32,
    general_purpose_event1_block: u32,

    // lengths of register blocks
    pm1_event_len: u8,
    pm1_control_len: u8,
    pm2_control_len: u8,
    pm_timer_len: u8,
    general_purpose_event0_len: u8,
    general_purpose_event1_len: u8,
    general_purpose_event1_base: u8,

    cstate_control: u8,
    worst_c2_latency: u16, // P_LVL2_LAT in spec
    worst_c3_latency: u16, // P_LVL3_LAT in spec

    // Maintained for ACPI 1.0 support
    flush_size: u16,
    flush_stride: u16,

    duty_offset: u8,
    duty_width: u8,
    day_alarm: u8,
    month_alarm: u8,
    century: u8,

    // Reserved in ACPI 1.0, used since ACPI 2.0+
    iapc_boot_arch_flags: u16,

    _reserved2: u8,

    fixed_feature_flags: u32,
    reset_register: GenericAddressStructure,

    // Reset reg port value for resetting the system
    reset_value: u8,

    // Irrelevant since we don't support ARM.
    arm_boot_arch_flags: u16,

    fadt_minor_version: u8,

    // If provided, ACPI spec requires prioritizing this over the 32-bit addresses
    pub extended_firmware_control: u64,
    pub extended_dsdt_address: u64,

    extended_pm1a_event_block: GenericAddressStructure,
    extended_pm1b_event_block: GenericAddressStructure,
    extended_pm1a_control_block: GenericAddressStructure,
    extended_pm1b_control_block: GenericAddressStructure,
    extended_pm2_control_block: GenericAddressStructure,
    extended_pm_timer_block: GenericAddressStructure,
    extended_general_purpose_event0_block: GenericAddressStructure,
    extended_general_purpose_event1_block: GenericAddressStructure,
}
static_assertions::assert_eq_size!(FadtAcpi2, [u8; 244usize]);

impl AcpiTable for FadtAcpi2 {
    type Signature = Signature;

    fn try_from_bytes(buf: &[u8]) -> Result<(&Self, &[u8])> {
        // First, try to parse the header, to determine the version.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid FADT header")?;

        if header.revision < 2 || header.revision > 4 {
            return Err("FADT ACPI revision not supported");
        }

        let (fadt, tail) = Self::try_ref_from_prefix(buf).map_err(|_| "invalid FADT")?;
        fadt.validate()?;
        Ok((fadt, tail))
    }

    fn try_from_bytes_mut(buf: &mut [u8]) -> Result<(&mut Self, &mut [u8])> {
        // First, try to parse the header, to determine the version.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid FADT header")?;

        if header.revision < 2 || header.revision > 4 {
            return Err("FADT ACPI revision not supported");
        }

        let (fadt, tail) = Self::try_mut_from_prefix(buf).map_err(|_| "invalid FADT")?;
        fadt.validate()?;
        Ok((fadt, tail))
    }

    fn header(&self) -> &DescriptionHeader<Self::Signature> {
        &self.header
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Self::Signature> {
        &mut self.header
    }
}

/// Fixed ACPI Description Table (FADT) for ACPI 5.0.
///
/// This is used for QEMU `microvm`.
#[derive(Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct FadtAcpi5 {
    fadt_acpi_2: FadtAcpi2,

    // ACPI 5.0 introduces extra flags SLEEP_CONTROL_REG and SLEEP_STATUS_REG:
    // https://uefi.org/sites/default/files/resources/ACPI_5_0_Errata_B.pdf
    sleep_control_register: GenericAddressStructure,
    sleep_status_register: GenericAddressStructure,
}
static_assertions::assert_eq_size!(FadtAcpi5, [u8; 268usize]);

impl Debug for FadtAcpi5 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("FADT")
            .field("fadt_acpi_2", &self.fadt_acpi_2)
            .field("sleep_control_register", &self.sleep_control_register)
            .field("sleep_status_register", &self.sleep_status_register)
            .finish()
    }
}

impl AcpiTable for FadtAcpi5 {
    type Signature = Signature;

    fn try_from_bytes(buf: &[u8]) -> Result<(&Self, &[u8])> {
        // First, try to parse the header, to determine the version.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid FADT header")?;

        if header.revision != 5 {
            return Err("FADT ACPI revision not supported");
        }

        let (fadt, tail) = Self::try_ref_from_prefix(buf).map_err(|_| "invalid FADT")?;
        fadt.validate()?;
        Ok((fadt, tail))
    }

    fn try_from_bytes_mut(buf: &mut [u8]) -> Result<(&mut Self, &mut [u8])> {
        // First, try to parse the header, to determine the version.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid FADT header")?;

        if header.revision != 5 {
            return Err("FADT ACPI revision not supported");
        }

        let (fadt, tail) = Self::try_mut_from_prefix(buf).map_err(|_| "invalid FADT")?;
        fadt.validate()?;
        Ok((fadt, tail))
    }

    fn header(&self) -> &DescriptionHeader<Self::Signature> {
        &self.fadt_acpi_2.header
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Self::Signature> {
        &mut self.fadt_acpi_2.header
    }
}

/// Fixed ACPI Description Table (FADT).
///
/// This is always the first entry of XSDT and is guaranteed to be in RSDT.
/// See Section 5.2.9 in the ACPI specification for more details.
/// Look to https://wiki.osdev.org/FADT for a reference implementation
#[derive(Immutable, IntoBytes, KnownLayout, TryFromBytes)]
#[repr(C, packed)]
pub struct FadtAcpi6 {
    // The Revision field in the header must be "6", otherwise the first fields are the same.
    fadt_acpi_5: FadtAcpi5,

    // ACPI 6.0 introduces the "Hypervisor Vendor Identity" field
    // https://uefi.org/sites/default/files/resources/ACPI_6.0.pdf
    hypervisor_vendor_identity: u64,
}
static_assertions::assert_eq_size!(FadtAcpi6, [u8; 276usize]);

impl Debug for FadtAcpi6 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let hypervisor_vendor_identity = self.hypervisor_vendor_identity;
        f.debug_struct("FADT")
            .field("fadt_acpi_5", &self.fadt_acpi_5)
            .field("hypervisor_vendor_identity", &hypervisor_vendor_identity)
            .finish()
    }
}

impl AcpiTable for FadtAcpi6 {
    type Signature = Signature;

    fn try_from_bytes(buf: &[u8]) -> Result<(&Self, &[u8])> {
        // First, try to parse the header, to determine the version.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid FADT header")?;

        if header.revision < 6 {
            return Err("FADT ACPI revision not supported");
        }

        let (fadt, tail) = Self::try_ref_from_prefix(buf).map_err(|_| "invalid FADT")?;
        if header.revision == 6 {
            fadt.validate()?;
        } else {
            log::warn!("ACPI FADT too new (>6), interpreting as ACPI 6");
        }
        Ok((fadt, tail))
    }

    fn try_from_bytes_mut(buf: &mut [u8]) -> Result<(&mut Self, &mut [u8])> {
        // First, try to parse the header, to determine the version.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid FADT header")?;

        let revision = header.revision;
        if revision < 6 {
            return Err("FADT ACPI revision not supported");
        }

        let (fadt, tail) = Self::try_mut_from_prefix(buf).map_err(|_| "invalid FADT")?;
        if revision == 6 {
            fadt.validate()?;
        } else {
            log::warn!("ACPI FADT too new (>6), interpreting as ACPI 6");
        }
        Ok((fadt, tail))
    }

    fn header(&self) -> &DescriptionHeader<Self::Signature> {
        &self.fadt_acpi_5.fadt_acpi_2.header
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Self::Signature> {
        &mut self.fadt_acpi_5.fadt_acpi_2.header
    }
}

// Note: this can't be `Fadt: AcpiTable` as that'd make `Fadt` not
// dyn-compatible (because of `try_ref_from_prefix` and other zerocopy friends).
pub trait Fadt: Checksum + Debug {
    fn header(&self) -> &DescriptionHeader<Signature>;
    fn header_mut(&mut self) -> &mut DescriptionHeader<Signature>;
}

impl Fadt for FadtAcpi2 {
    fn header(&self) -> &DescriptionHeader<Signature> {
        AcpiTable::header(self)
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Signature> {
        AcpiTable::header_mut(self)
    }
}
impl Fadt for FadtAcpi5 {
    fn header(&self) -> &DescriptionHeader<Signature> {
        AcpiTable::header(self)
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Signature> {
        AcpiTable::header_mut(self)
    }
}
impl Fadt for FadtAcpi6 {
    fn header(&self) -> &DescriptionHeader<Signature> {
        AcpiTable::header(self)
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Signature> {
        AcpiTable::header_mut(self)
    }
}

impl AcpiTable for dyn Fadt {
    type Signature = Signature;

    fn try_from_bytes_mut(buf: &mut [u8]) -> Result<(&mut Self, &mut [u8])> {
        // First, try to parse the header, to determine the version.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid FADT header")?;

        match header.revision {
            ..=1 => Err("FADT ACPI revision not supported"),
            2..=4 => {
                FadtAcpi2::try_from_bytes_mut(buf).map(|(fadt, tail)| (fadt as &mut dyn Fadt, tail))
            }
            5 => {
                FadtAcpi5::try_from_bytes_mut(buf).map(|(fadt, tail)| (fadt as &mut dyn Fadt, tail))
            }
            6.. => {
                FadtAcpi6::try_from_bytes_mut(buf).map(|(fadt, tail)| (fadt as &mut dyn Fadt, tail))
            }
        }
    }

    fn try_from_bytes(buf: &[u8]) -> Result<(&Self, &[u8])> {
        // First, try to parse the header, to determine the version.
        let (header, _) = DescriptionHeader::<Signature>::try_ref_from_prefix(buf)
            .map_err(|_| "invalid FADT header")?;

        match header.revision {
            ..=1 => Err("FADT ACPI revision not supported"),
            2..=4 => FadtAcpi2::try_from_bytes(buf).map(|(fadt, tail)| (fadt as &dyn Fadt, tail)),
            5 => FadtAcpi5::try_from_bytes(buf).map(|(fadt, tail)| (fadt as &dyn Fadt, tail)),
            6.. => FadtAcpi6::try_from_bytes(buf).map(|(fadt, tail)| (fadt as &dyn Fadt, tail)),
        }
    }

    fn header(&self) -> &DescriptionHeader<Self::Signature> {
        Fadt::header(self)
    }

    fn header_mut(&mut self) -> &mut DescriptionHeader<Self::Signature> {
        Fadt::header_mut(self)
    }
}

#[cfg(test)]
mod tests {
    use googletest::prelude::*;

    use super::*;

    // This FADT is obtained from a machine running on GCP.
    const FADT: &[u8] = &[
        0x46, 0x41, 0x43, 0x50, 0xf4, 0x00, 0x00, 0x00, 0x02, 0x99, 0x47, 0x6f, 0x6f, 0x67, 0x6c,
        0x65, 0x47, 0x4f, 0x4f, 0x47, 0x46, 0x41, 0x43, 0x50, 0x01, 0x00, 0x00, 0x00, 0x47, 0x4f,
        0x4f, 0x47, 0x01, 0x00, 0x00, 0x00, 0x80, 0xd8, 0xff, 0x3f, 0xc0, 0xd8, 0xff, 0x3f, 0x01,
        0x00, 0x09, 0x00, 0xb2, 0x00, 0x00, 0x00, 0xf1, 0xf0, 0x00, 0x00, 0x00, 0xb0, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x04, 0xb0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x08, 0xb0, 0x00, 0x00, 0xe0, 0xaf, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x02,
        0x00, 0x04, 0x04, 0x00, 0x00, 0x00, 0xff, 0x0f, 0xff, 0x0f, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x85, 0x84, 0x00, 0x00, 0x01, 0x08, 0x00, 0x00,
        0xf9, 0x0c, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x06, 0x00, 0x00, 0x00, 0x80, 0xd8, 0xff,
        0x3f, 0x00, 0x00, 0x00, 0x00, 0xc0, 0xd8, 0xff, 0x3f, 0x00, 0x00, 0x00, 0x00, 0x01, 0x20,
        0x00, 0x00, 0x00, 0xb0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x10, 0x00, 0x00, 0x04, 0xb0, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x20,
        0x00, 0x00, 0x08, 0xb0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x20, 0x00, 0x00, 0xe0,
        0xaf, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00,
    ];

    #[test]
    fn test_generic_parse() {
        assert_that!(<dyn Fadt>::try_from_bytes(FADT), ok(anything()));
    }

    #[test]
    fn test_parse_acpi_2_table() {
        let (fadt, _) = FadtAcpi2::try_from_bytes(FADT).unwrap();
        assert_that!(
            fadt,
            matches_pattern!(FadtAcpi2 {
                header: matches_pattern!(DescriptionHeader::<Signature> {
                    revision: eq(&2),
                    oem_id: eq(b"Google"),
                    oem_table_id: eq(b"GOOGFACP"),
                    ..
                }),
                fadt_minor_version: eq(&0),
                ..
            })
        )
    }
}
