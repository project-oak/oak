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

use core::arch::x86_64::__cpuid;

use bitflags::bitflags;
use x86_64::{registers::model_specific::Msr, PhysAddr};

bitflags! {
    /// Flags in the APIC Base Address Register (MSR 0x1B)
    #[derive(Clone, Copy, Debug)]
    pub struct ApicBaseFlags: u64 {
        /// APIC Enable
        ///
        /// The local APIC is enabled and all interruption types are accepted.
        const AE = (1 << 11);

        /// x2APIC Mode Enable
        ///
        /// The local APIC must first be enabled before enabling x2APIC mode.
        /// Support for x2APIC mode is indicated by CPUID Fn0000_0001_ECX[21] = 1.
        const EXTD = (1 << 10);

        /// Boot Strap CPU Core
        ///
        /// Indicates that this CPU core is the boot core of the BSP.
        const BSC = (1 << 8);
    }
}

/// The APIC Base Address Register.
///
/// See Sections 16.3.1 (Local APIC Enable) and 16.9 (Detecting and Enabling x2APIC Mode) in the
/// AMD64 Architecture Programmer's Manual, Volume 2 for more details.
pub struct ApicBase;

impl ApicBase {
    pub const MSR: Msr = Msr::new(0x0000_001B);

    fn read_raw() -> u64 {
        // Safety: the APIC base register is supported in all modern CPUs.
        unsafe { Self::MSR.read() }
    }

    fn write_raw(value: u64) {
        let mut msr = Self::MSR;
        // Safety: the APIC base register is supported in all modern CPUs.
        unsafe { msr.write(value) }
    }

    /// Returns the APIC Base Address and flags.
    pub fn read() -> (PhysAddr, ApicBaseFlags) {
        let val = Self::read_raw();
        let apa = PhysAddr::new(val & 0x000F_FFFF_FFFF_F000u64);
        let flags = ApicBaseFlags::from_bits_truncate(val);

        (apa, flags)
    }

    pub fn write(apa: PhysAddr, flags: ApicBaseFlags) {
        Self::write_raw(flags.bits() | apa.as_u64());
    }
}

/// The x2APIC_ID register.
///
/// Contains the 32-bit local x2APIC ID. It is assigned by hardware at reset time, and the exact
/// structure is manufacturer-dependent.
///
/// See Section 16.12 (x2APIC_ID) in the AMD64 Architecture Programmer's Manual, Volume 2 for more
/// details.
pub struct X2ApicIdRegister;

impl X2ApicIdRegister {
    pub const MSR: Msr = Msr::new(0x0000_0802);

    fn read_raw() -> u64 {
        // Safety: this is safe to read if the system supports x2APIC.
        unsafe { Self::MSR.read() }
    }

    pub fn read() -> u32 {
        Self::read_raw() as u32
    }
}

/// Interrupt Command Register.
///
/// Used to send inter-processor interrupts (IPIs) to other cores in the system.
///
/// See Section 16.5 (Interprocessor Interrupts) and Section 16/13 (x2APIC Interrupt Command
/// Register Operations) in the AMD64 Architecture Programmer's Manual, Volume 2 for more details.
pub struct InterruptCommandRegister;

/// Interrupt types that can be sent via the Interrupt Command Register.
///
/// Note that this enum contains only values supported by x2APIC; the legacy xAPIC supports some
/// extra message types that are deprecated (and reserved) under x2APIC.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture Programmer's Manual,
/// Volume 2 for more details.
#[allow(dead_code, clippy::upper_case_acronyms)]
pub enum MessageType {
    /// IPI delivers an interrupt to the target local APIC specified in the Destination field.
    Fixed = 0b000,

    /// IPI delivers an SMI interrupt to the target local APIC(s). Trigger mode is edge-triggered
    /// and Vector must be 0x00.
    SMI = 0b010,

    // IPI delivers an non-maskable interrupt to the target local APIC specified in the
    // Destination field. Vector is ignored.
    NMI = 0b100,

    /// IPI delivers an INIT request to the target local APIC(s), causing the CPU core to assume
    /// INIT state. Trigger mode is edge-triggered, Vector must be 0x00. After INIT, target APIC
    /// will only accept a Startup IPI, all other interrupts will be held pending.
    Init = 0b101,

    /// IPI delives a start-up request (SIPI) to the target local APIC(s) in the Destination field,
    /// causing the core to start processing the routing whose address is specified by the Vector
    /// field.
    Startup = 0b110,
}

/// Values for the destination mode flag in the Interrupt Command Register.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture Programmer's Manual,
/// Volume 2 for more details.
#[allow(dead_code)]
pub enum DestinationMode {
    // Physical destination, single local APIC ID.
    Physical = 0,

    /// Logical destination, one or more local APICs with a common destination logical ID.
    Logical = 1,
}

/// Values for the level flag in the Interrupt Command Register.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture Programmer's Manual,
/// Volume 2 for more details.
pub enum Level {
    Deassert = 0,
    Assert = 1,
}

/// Values for the trigger mode flag in the Interrupt Command Register.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture Programmer's Manual,
/// Volume 2 for more details.
pub enum TriggerMode {
    Edge = 0,
    Level = 1,
}

/// Values for the destination shorthand flag in the Interrupt Command Register.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture Programmer's Manual,
/// Volume 2 for more details.
#[allow(dead_code)]
pub enum DestinationShorthand {
    /// Destination field is required to specify the destination.
    DestinationField = 0b00,

    /// The issuing APIC is the only destination.
    SelfOnly = 0b01,

    /// The IPI is sent to all local APICs including itself (destination field = 0xFF)
    AllInclSelf = 0b10,

    /// The IPI is sent to all local APICs except itself (destination field = 0xFF)
    AllExclSelf = 0b11,
}

impl InterruptCommandRegister {
    pub const MSR: Msr = Msr::new(0x0000_00830);

    fn write_raw(value: u64) {
        let mut msr = Self::MSR;
        // Safety: this MSR is safe to access if the system supports x2APIC.
        unsafe { msr.write(value) }
    }

    /// Sends an IPI (inter-processor interrupt) to another LAPIC in the system.
    pub fn write(
        destination: u32,
        vector: u8,
        message_type: MessageType,
        destination_mode: DestinationMode,
        level: Level,
        trigger_mode: TriggerMode,
        destination_shorthand: DestinationShorthand,
    ) {
        let mut value: u64 = (destination as u64) << 32;
        value |= (destination_shorthand as u64) << 18;
        value |= (trigger_mode as u64) << 15;
        value |= (level as u64) << 14;
        value |= (destination_mode as u64) << 11;
        value |= (message_type as u64) << 8;
        value |= vector as u64;
        Self::write_raw(value)
    }
}

/// APIC Error Status Register.
///
/// See Section 16.4.6 (APIC Error Interrupts) in the AMD64 Architecture Programmer's Manual, Volume
/// 2 for more details.
pub struct ErrorStatusRegister;

impl ErrorStatusRegister {
    pub const MSR: Msr = Msr::new(0x0000_00828);

    fn write_raw(value: u64) {
        let mut msr = Self::MSR;
        // Safety: this MSR is safe to write if the system supports x2APIC.
        unsafe { msr.write(value) }
    }

    pub fn clear() {
        Self::write_raw(0);
    }
}

/// Wrapper for the local APIC.
///
/// Currenty only supports x2APIC mode.
pub struct Lapic {}

impl Lapic {
    pub fn enable() -> Result<Self, &'static str> {
        // Safety: the CPUs we support are new enough to support CPUID.
        let result = unsafe { __cpuid(0x0000_0001) };
        if result.ecx & (1 << 21) == 0 {
            return Err("x2APIC not supported");
        }
        // See Section 16.9 in the AMD64 Architecture Programmer's Manual, Volume 2 for explanation
        // of the initialization procedure.
        let (apa, mut flags) = ApicBase::read();
        if !flags.contains(ApicBaseFlags::AE) {
            flags |= ApicBaseFlags::AE;
            ApicBase::write(apa, flags);
        }
        if !flags.contains(ApicBaseFlags::EXTD) {
            flags |= ApicBaseFlags::EXTD;
            ApicBase::write(apa, flags);
        }

        Ok(Lapic {})
    }

    /// Sends an INIT IPI to the local APIC specified by `destination`.
    pub fn send_init_ipi(&self, destination: u32) {
        ErrorStatusRegister::clear();
        InterruptCommandRegister::write(
            destination,
            0,
            MessageType::Init,
            DestinationMode::Physical,
            Level::Assert,
            TriggerMode::Edge,
            DestinationShorthand::DestinationField,
        );
        InterruptCommandRegister::write(
            destination,
            0,
            MessageType::Init,
            DestinationMode::Physical,
            Level::Deassert,
            TriggerMode::Edge,
            DestinationShorthand::DestinationField,
        );
    }

    /// Sends a STARTUP IPI (SIPI) to the local APIC specified by `destination`.
    pub fn send_startup_ipi(&self, destination: u32, vector: PhysAddr) -> Result<(), &'static str> {
        if !vector.is_aligned(0x1000u64) {
            return Err("startup vector is not page-aligned");
        }
        let vector = vector.as_u64();
        if vector > 0x100000 {
            return Err("startup vector needs to be in the first megabyte of memory");
        }
        ErrorStatusRegister::clear();
        InterruptCommandRegister::write(
            destination,
            (vector / 0x1000) as u8,
            MessageType::Startup,
            DestinationMode::Physical,
            Level::Assert,
            TriggerMode::Level,
            DestinationShorthand::DestinationField,
        );
        Ok(())
    }
}
