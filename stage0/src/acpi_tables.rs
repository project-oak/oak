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

use core::{fmt::Debug, mem::size_of};

use crate::acpi::tables::DescriptionHeader;

type ResultStaticErr<T> = Result<T, &'static str>;

// GAS for short. This is a structure used to describe the position of
// registers.
#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
pub struct GenericAddressStructure {
    address_space: u8,
    bit_width: u8,
    bit_offset: u8,
    access_size: u8,
    address: u64,
}
static_assertions::assert_eq_size!(GenericAddressStructure, [u8; 12usize]);

/// Fixed ACPI Description Table (FADT).
///
/// This is always the first entry of XSDT and is guaranteed to be in RSDT.
/// See Section 5.2.9 in the ACPI specification for more details.
/// Look to https://wiki.osdev.org/FADT for a reference implementation
#[derive(Debug)]
#[repr(C, packed)]
pub struct Fadt {
    // In FADT's table, the revision field actually refers to the FADT's major version
    pub header: DescriptionHeader,
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

    // Depending on the revision, the fields below are not present.
    // This is annoying because we will overread the buffer if the
    // latest ACPI table is not passed, but given that these fields are largely
    // irrelevant, we can ignore usage of these fields. If needed, we can
    // provide accessor methods to gate on this usage.

    // ACPI 5.0 introduces extra flags SLEEP_CONTROL_REG and SLEEP_STATUS_REG:
    // https://uefi.org/sites/default/files/resources/ACPI_5_0_Errata_B.pdf
    sleep_control_register: GenericAddressStructure,
    sleep_status_register: GenericAddressStructure,

    // ACPI 6.0 introduces the "Hypervisor Vendor Identity" field
    // https://uefi.org/sites/default/files/resources/ACPI_6.0.pdf
    hypervisor_vendor_identity: u64,
}
// Make this comparison against the ACPI 6.0 spec. In validate() we will account
// for older revisions
static_assertions::assert_eq_size!(Fadt, [u8; 276usize]);

impl Fadt {
    // Unlike other tables, this has a different signature
    // compared to its intended name because it predates ACPI 1.0
    pub const SIGNATURE: &'static [u8; 4] = b"FACP";

    pub fn new(hdr: &DescriptionHeader) -> ResultStaticErr<&'static Fadt> {
        // Safety: we're checking that it's a valid FADT in `validate()`.
        let fadt = unsafe { &*(hdr as *const _ as usize as *const Fadt) };
        fadt.validate()?;
        Ok(fadt)
    }

    /// Sets checksum field so that checksum validates.
    /// To be called after modifying any of this structures's data.
    #[allow(dead_code)]
    pub fn update_checksum(&mut self) {
        self.header.update_checksum();
    }

    fn validate(&self) -> ResultStaticErr<()> {
        self.header.validate()?;

        if self.header.signature != *Self::SIGNATURE {
            return Err("Invalid signature for FADT table");
        }

        // Depending on the major version provided in the FADT, this is subject to
        // change. We adjust the check based on the major version
        let acpi_6_length = size_of::<Fadt>() as u32;
        let expected_table_size = if self.header.revision == 6 {
            acpi_6_length
        } else if self.header.revision == 5 {
            acpi_6_length - size_of::<u64>() as u32
        } else if self.header.revision < 5 {
            acpi_6_length
                - size_of::<u64>() as u32
                - 2 * size_of::<GenericAddressStructure>() as u32
        } else {
            return Err("Unexpected ACPI major version");
        };

        if self.header.length != expected_table_size {
            log::error!(
                "FADT header length did not match the expected table struct size. Expected: {}, got: {:#x}",
                expected_table_size,
                { self.header.length }
            );
            return Err("FADT header length did not match the expected table struct size.");
        }

        Ok(())
    }
}
