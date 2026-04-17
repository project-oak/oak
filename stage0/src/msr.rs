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

use bitflags::bitflags;
use strum::FromRepr;
use x86_64::PhysAddr;

use crate::{Platform, hal::Msr};

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
/// See Sections 16.3.1 (Local APIC Enable) and 16.9 (Detecting and Enabling
/// x2APIC Mode) in the AMD64 Architecture Programmer's Manual, Volume 2 for
/// more details.
pub struct ApicBase;

impl ApicBase {
    const MSR: Msr = Msr::new(0x0000_001B);

    fn write_raw<P: Platform>(value: u64) {
        let mut msr = Self::MSR;
        // Safety: the APIC base register is supported in all modern CPUs.
        unsafe { msr.write::<P>(value) }
    }

    /// Returns the APIC Base Address and flags.
    pub fn read<P: Platform>() -> (PhysAddr, ApicBaseFlags) {
        // Safety: the APIC base register is supported in all modern CPUs.
        let val = unsafe { Self::MSR.read::<P>() };
        let aba = PhysAddr::new(val & 0x000F_FFFF_FFFF_F000u64);
        let flags = ApicBaseFlags::from_bits_truncate(val);

        (aba, flags)
    }

    pub fn write<P: Platform>(aba: PhysAddr, flags: ApicBaseFlags) {
        Self::write_raw::<P>(flags.bits() | aba.as_u64());
    }
}

bitflags! {
    /// Flags of the MTRRDefType Register.
    pub struct MTRRDefTypeFlags: u64 {
        /// Set this to enable MTRR.
        const MTRR_ENABLE = 1 << 11;
        /// Set to enable fixed-range support.
        const FIXED_RANGE_ENABLE = 1 << 10;
    }
}

/// The cache memory type used with MTRR.  We only use Write-Protect mode which
/// the Linux kernel expects to be enabled by the firmware in order to enable
/// SEV.
#[repr(u8)]
#[allow(dead_code)] // Remove if this is ever ported to a public crate.
#[derive(FromRepr)]
pub enum MemoryType {
    UC = 0, // Uncacheable.
    WC = 1, // Write-Combining.
    WT = 4, // Writethrough	Reads.
    WP = 5, // Write-Protect.
    WB = 6, // Writeback.
}

impl TryFrom<u8> for MemoryType {
    type Error = &'static str;
    fn try_from(value: u8) -> Result<MemoryType, &'static str> {
        MemoryType::from_repr(value).ok_or("invalid value for MemoryType")
    }
}

/// IA32_MTRR_DefType base model specific register.
/// See <https://wiki.osdev.org/MTRR> for documentation.
#[derive(Debug)]
pub struct MTRRDefType;

impl MTRRDefType {
    // The underlying model specific register.
    const MSR: Msr = Msr::new(0x0000_02FF);

    pub fn read<P: Platform>() -> (MTRRDefTypeFlags, MemoryType) {
        // If the GHCB is available we are running on SEV-ES or SEV-SNP, so we use the
        // GHCB protocol to read the MSR, otherwise we read the MSR directly.
        // Safety: This is safe because this MSR has been supported since the P6 family
        // of Pentium processors (see https://en.wikipedia.org/wiki/Memory_type_range_register).
        let msr_value = unsafe { Self::MSR.read::<P>() };
        let memory_type: MemoryType =
            (msr_value as u8).try_into().expect("invalid MemoryType value");
        (MTRRDefTypeFlags::from_bits_truncate(msr_value), memory_type)
    }

    /// Write the MTRRDefType flags and caching mode, preserving reserved
    /// values. The Linux kernel requires the mode be set to
    /// `MemoryType::WP` since July, 2022, with this requirement back-ported
    /// to 5.15.X, or it will silently crash when SEV is enabled.
    ///
    /// The Linux kernel gives a warning that MTRR is not setup properly, which
    /// we can igore: [    0.120763] mtrr: your CPUs had inconsistent
    /// MTRRdefType settings [    0.121529] mtrr: probably your BIOS does
    /// not setup all CPUs. [    0.122245] mtrr: corrected configuration.
    ///
    /// ## Safety
    ///
    /// Unsafe in rare cases such as when ROM is memory mapped, and we write to
    /// ROM, in a mode that caches the write, although this would require
    /// unsafe code to do.
    ///
    /// When called with MTRRDefType::MTRR_ENABLE and MemoryType::WP, this
    /// operation is safe because this specific MSR and mode has been
    /// supported since the P6 family of Pentium processors (see <https://en.wikipedia.org/wiki/Memory_type_range_register>).
    pub unsafe fn write<P: Platform>(flags: MTRRDefTypeFlags, default_type: MemoryType) {
        // Preserve values of reserved bits.
        let (old_flags, _old_memory_type) = Self::read::<P>();
        let reserved = old_flags.bits() & !MTRRDefTypeFlags::all().bits();
        let new_value = reserved | flags.bits() | (default_type as u64);
        let mut msr = Self::MSR;
        unsafe { msr.write::<P>(new_value) };
    }
}

/// The x2APIC_ID register.
///
/// Contains the 32-bit local x2APIC ID. It is assigned by hardware at reset
/// time, and the exact structure is manufacturer-dependent.
///
/// See Section 16.12 (x2APIC_ID) in the AMD64 Architecture Programmer's Manual,
/// Volume 2 for more details.
pub struct X2ApicIdRegister;

impl X2ApicIdRegister {
    const MSR: Msr = Msr::new(0x0000_00802);

    /// # Safety
    ///   - X2ApicIdRegister must be present on this system.
    pub unsafe fn apic_id<P: Platform>() -> u32 {
        unsafe { (Self::MSR.read::<P>() & 0xFFFF_FFFF) as u32 }
    }
}

/// x2APIC APIC Version Register
pub struct X2ApicVersionRegister;

impl X2ApicVersionRegister {
    const MSR: Msr = Msr::new(0x0000_0803);
}

impl X2ApicVersionRegister {
    /// # Safety
    ///   - X2ApicVersionRegister must be present on this system.
    pub unsafe fn read<P: Platform>() -> (bool, u8, u8) {
        let val = unsafe { Self::MSR.read::<P>() };

        (
            val & (1 << 31) > 0,            // EAS
            ((val & 0xFF0000) >> 16) as u8, // MLE
            (val & 0xFF) as u8,             // VER
        )
    }
}

bitflags! {
    /// Flags in the Spurious Interrupt Register (offset 0x0F0)
    ///
    /// See Section 16.4.7, Spurious Interrupts, in the AMD64 Architecture Programmer's Manual, Volume 2 for more details.
    #[derive(Clone, Copy, Debug)]
    pub struct SpuriousInterruptFlags: u32 {
        /// APIC Software Enable
        const ASE = (1 << 8);

        /// Focus CPU Core Checking
        const FCC = (1 << 9);
    }
}

/// x2APIC Spurious Interrupt Register
pub struct X2ApicSpuriousInterruptRegister;

impl X2ApicSpuriousInterruptRegister {
    const MSR: Msr = Msr::new(0x0000_080F);
}

impl X2ApicSpuriousInterruptRegister {
    /// # Safety
    ///   - X2ApicSpuriousInterruptRegister must be present on this system.
    pub unsafe fn read<P: Platform>() -> (SpuriousInterruptFlags, u8) {
        let val = unsafe { Self::MSR.read::<P>() };

        (SpuriousInterruptFlags::from_bits_truncate((val & 0xFFFF_FF00) as u32), (val & 0xFF) as u8)
    }

    /// # Safety
    ///   - X2ApicSpuriousInterruptRegister must be present on this system.
    pub unsafe fn write<P: Platform>(flags: SpuriousInterruptFlags, vec: u8) {
        // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
        let val = flags.bits() as u64 | vec as u64;
        let mut msr = Self::MSR;
        unsafe { msr.write::<P>(val) };
    }
}

bitflags! {
    /// Flags in the APIC Error Status Register (offset 0x280)
    ///
    /// See Section 16.4.6, APIC Error Interrupts, in the AMD64 Architecture Programmer's Manual, Volume 2 for more details.
    #[derive(Clone, Copy, Debug)]
    pub struct ApicErrorFlags: u32 {
        /// Sent Accept Error
        ///
        /// Message sent by the local APIC was not accepted by any other APIC.
        const SAE = (1 << 2);

        /// Receive Accept Error
        ///
        /// Message received by the local APIC was not accepted by this or any other APIC.
        const RAE = (1 << 3);

        /// Sent Illegal Vector
        ///
        /// Local APIC attempted to send a message with an illegal vector value.
        const SIV = (1 << 5);

        /// Received Illegal Vector
        ///
        /// Local APIC has received a message with an illegal vector value.
        const RIV = (1 << 6);

        /// Illegal Register Address
        ///
        /// An access to an unimplementer registed within the APIC register range was attempted.
        const IRA = (1 << 7);
    }
}

/// x2APIC Error Status Register.
pub struct X2ApicErrorStatusRegister;

impl X2ApicErrorStatusRegister {
    const MSR: Msr = Msr::new(0x0000_0828);
}

impl X2ApicErrorStatusRegister {
    /// # Safety
    ///   - X2ApicIdRegister must be present on this system.
    #[allow(unused)]
    pub unsafe fn read<P: Platform>() -> ApicErrorFlags {
        let val = unsafe { Self::MSR.read::<P>() };
        ApicErrorFlags::from_bits_truncate(val.try_into().unwrap())
    }

    /// # Safety
    ///   - X2ApicIdRegister must be present on this system.
    pub unsafe fn write<P: Platform>(val: ApicErrorFlags) {
        let mut msr = Self::MSR;
        unsafe { msr.write::<P>(val.bits() as u64) }
    }

    /// # Safety
    ///   - X2ApicIdRegister must be present on this system.
    pub unsafe fn clear<P: Platform>() {
        unsafe { Self::write::<P>(ApicErrorFlags::empty()) }
    }
}

/// Interrupt types that can be sent via the Interrupt Command Register.
///
/// Note that this enum contains only values supported by x2APIC; the legacy
/// xAPIC supports some extra message types that are deprecated (and reserved)
/// under x2APIC.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
#[allow(dead_code, clippy::upper_case_acronyms)]
#[repr(u32)]
pub enum MessageType {
    /// IPI delivers an interrupt to the target local APIC specified in the
    /// Destination field.
    Fixed = 0b000 << 8,

    /// IPI delivers an SMI interrupt to the target local APIC(s). Trigger mode
    /// is edge-triggered and Vector must be 0x00.
    SMI = 0b010 << 8,

    // IPI delivers an non-maskable interrupt to the target local APIC specified in the
    // Destination field. Vector is ignored.
    NMI = 0b100 << 8,

    /// IPI delivers an INIT request to the target local APIC(s), causing the
    /// CPU core to assume INIT state. Trigger mode is edge-triggered,
    /// Vector must be 0x00. After INIT, target APIC will only accept a
    /// Startup IPI, all other interrupts will be held pending.
    Init = 0b101 << 8,

    /// IPI delives a start-up request (SIPI) to the target local APIC(s) in the
    /// Destination field, causing the core to start processing the routing
    /// whose address is specified by the Vector field.
    Startup = 0b110 << 8,
}

/// Values for the destination mode flag in the Interrupt Command Register.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
#[allow(dead_code)]
#[repr(u32)]
pub enum DestinationMode {
    // Physical destination, single local APIC ID.
    Physical = 0 << 11,

    /// Logical destination, one or more local APICs with a common destination
    /// logical ID.
    Logical = 1 << 11,
}

/// Values for the level flag in the Interrupt Command Register.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
#[repr(u32)]
pub enum Level {
    Deassert = 0 << 14,
    Assert = 1 << 14,
}

/// Values for the trigger mode flag in the Interrupt Command Register.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
#[repr(u32)]
pub enum TriggerMode {
    Edge = 0 << 15,
    Level = 1 << 15,
}

/// Values for the destination shorthand flag in the Interrupt Command Register.
///
/// See Section 16.5 (Interprocessor Interrupts) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
#[allow(dead_code)]
#[repr(u32)]
pub enum DestinationShorthand {
    /// Destination field is required to specify the destination.
    DestinationField = 0b00 << 18,

    /// The issuing APIC is the only destination.
    SelfOnly = 0b01 << 18,

    /// The IPI is sent to all local APICs including itself (destination field =
    /// 0xFF)
    AllInclSelf = 0b10 << 18,

    /// The IPI is sent to all local APICs except itself (destination field =
    /// 0xFF)
    AllExclSelf = 0b11 << 18,
}

/// x2APIC Interrupt Command Register.
///
/// Merges the two xAPIC ICR-s into one 64-bit MSR.
pub struct X2ApicInterruptCommandRegister;

impl X2ApicInterruptCommandRegister {
    const MSR: Msr = Msr::new(0x0000_00830);

    /// # Safety
    ///   - X2ApicInterruptCommandRegister must be present on this system.
    pub unsafe fn send<P: Platform>(
        vec: u8,
        mt: MessageType,
        dm: DestinationMode,
        l: Level,
        tmg: TriggerMode,
        dsh: DestinationShorthand,
        dest: u32,
    ) {
        let mut value: u64 = (dest as u64) << 32;
        value |= dsh as u64;
        value |= tmg as u64;
        value |= l as u64;
        value |= dm as u64;
        value |= mt as u64;
        value |= vec as u64;

        let mut msr = Self::MSR;
        unsafe { msr.write::<P>(value) }
    }
}
