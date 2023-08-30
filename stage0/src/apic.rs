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
use core::arch::x86_64::__cpuid;
use x86_64::{registers::model_specific::Msr, PhysAddr};

/// Interrupt Command.
///
/// Used to send inter-processor interrupts (IPIs) to other cores in the system.
///
/// See Section 16.5 (Interprocessor Interrupts) and Section 16/13 (x2APIC Interrupt Command
/// Register Operations) in the AMD64 Architecture Programmer's Manual, Volume 2 for more details.
trait InterprocessorInterrupt {
    /// Sends an IPI (inter-processor interrupt) to another LAPIC in the system.
    #[allow(clippy::too_many_arguments)]
    fn send(
        &mut self,
        destination: u32,
        vector: u8,
        message_type: MessageType,
        destination_mode: DestinationMode,
        level: Level,
        trigger_mode: TriggerMode,
        destination_shorthand: DestinationShorthand,
    ) -> Result<(), &'static str>;
}

/// APIC Error Status.
///
/// See Section 16.4.6 (APIC Error Interrupts) in the AMD64 Architecture Programmer's Manual,
/// Volume 2 for more details.
trait ErrorStatus {
    fn read(&self) -> ApicErrorFlags;
    fn clear(&mut self);
}

/// LAPIC identifier.
///
/// For APIC, it's 4 bits; xAPIC, 8 bits; x2APIC, 32 bits.
trait ApicId {
    fn apic_id(&self) -> u32;
}

/// APIC Version.
///
/// See Section 16.3.4 (APIC Version Register) in the AMD64 Architecture Programmer's Manual,
/// Volume 2 for more details.
trait ApicVersion {
    fn read(&self) -> (bool, u8, u8);
}

/// APIC spurious interrupt register.
///
/// See Section 16.4.7 (Spurious Interrupts) in the AMD64 Architecture Programmer's Manual,
/// Volume 2 for more details.
trait SpuriousInterrupts {
    fn read(&self) -> (SpuriousInterruptFlags, u8);
    fn write(&mut self, flags: SpuriousInterruptFlags, vec: u8);
}

mod xapic {
    use crate::paging::PAGE_TABLE_REFS;
    use core::mem::MaybeUninit;
    use x86_64::{
        instructions::tlb::flush_all,
        structures::paging::{PageSize, PageTableFlags, Size2MiB, Size4KiB},
        PhysAddr, VirtAddr,
    };

    use super::{ApicErrorFlags, SpuriousInterruptFlags};

    /// Wrapper for a MMIO register in memory.
    #[repr(transparent)]
    struct ApicRegister(u32);

    impl ApicRegister {
        fn read(&self) -> u32 {
            // Safety: these registers can only be accessed through ApicRegisters, by which we
            // should have established where the MMIO area is.
            unsafe { (self as *const _ as *const u32).read_volatile() }
        }
        fn write(&mut self, val: u32) {
            // Safety: these registers can only be accessed through ApicRegisters, by which we
            // should have established where the MMIO area is.
            unsafe { (self as *mut _ as *mut u32).write_volatile(val) }
        }
    }

    /// Representation of the APIC MMIO registers.
    ///
    /// We do not represent _all_ the xAPIC registers here, but only the ones we are interested in.
    ///
    /// The exact layout is defined in Table 16-2 and Section 16.3.2 (APIC Registers) of the AMD64
    /// Architecture Programmer's Manual, Volume 2.
    #[repr(C, align(4096))]
    pub(crate) struct ApicRegisters {
        _reserved: [u8; 0x20],                         // [0x000..0x020)
        apic_id_register: ApicRegister,                // [0x020..0x024)
        _reserved_2: [u8; 0xc],                        // [0x024..0x030)
        apic_version_register: ApicRegister,           // [0x030..0x034)
        _reserved_3: [u8; 0xbc],                       // [0x034..0x0F0)
        spurious_interrupt_register: ApicRegister,     // [0x0F0..0x0F4)
        _reserved_4: [u8; 0x18c],                      // [0x0F4..0x280)
        error_status_register: ApicRegister,           // [0x280..0x284)
        _reserved_5: [u8; 0x7c],                       // [0x284..0x300]
        interrupt_command_register_low: ApicRegister,  // [0x300..0x304)
        _reserved_6: [u8; 0xc],                        // [0x304..0x310)
        interrupt_command_register_high: ApicRegister, // [0x310..0x314)
        _padding: [u8; 0xcec],                         // [0x314..0x1000)
    }
    static_assertions::assert_eq_size!(ApicRegisters, [u8; Size4KiB::SIZE as usize]);

    impl super::ApicId for ApicRegisters {
        /// Read the Local APIC ID register.
        ///
        /// See Section 16.3.3 in the AMD64 Architecture Programmer's Manual, Volume 2 for the
        /// register format.
        fn apic_id(&self) -> u32 {
            self.apic_id_register.read() >> 24
        }
    }

    impl super::InterprocessorInterrupt for ApicRegisters {
        fn send(
            &mut self,
            destination: u32,
            vector: u8,
            message_type: super::MessageType,
            destination_mode: super::DestinationMode,
            level: super::Level,
            trigger_mode: super::TriggerMode,
            destination_shorthand: super::DestinationShorthand,
        ) -> Result<(), &'static str> {
            let destination: u8 = destination
                .try_into()
                .map_err(|_| "destination APIC ID too big for xAPIC")?;
            self.interrupt_command_register_high
                .write((destination as u32) << 24);
            self.interrupt_command_register_low.write(
                (destination_shorthand as u32) << 18
                    | (trigger_mode as u32) << 15
                    | (level as u32) << 14
                    | (destination_mode as u32) << 11
                    | (message_type as u32) << 8
                    | vector as u32,
            );
            Ok(())
        }
    }

    impl super::ErrorStatus for ApicRegisters {
        fn read(&self) -> ApicErrorFlags {
            ApicErrorFlags::from_bits_truncate(self.error_status_register.read())
        }

        fn clear(&mut self) {
            self.error_status_register.write(0)
        }
    }

    impl super::ApicVersion for ApicRegisters {
        fn read(&self) -> (bool, u8, u8) {
            let val = self.apic_version_register.read();

            (
                val & (1 << 31) > 0,            // EAS
                ((val & 0xFF0000) >> 16) as u8, // MLE
                (val & 0xFF) as u8,             // VER
            )
        }
    }

    impl super::SpuriousInterrupts for ApicRegisters {
        fn read(&self) -> (SpuriousInterruptFlags, u8) {
            let val = self.spurious_interrupt_register.read();

            (
                SpuriousInterruptFlags::from_bits_truncate(val),
                (val & 0xFF) as u8,
            )
        }

        fn write(&mut self, flags: super::SpuriousInterruptFlags, vec: u8) {
            self.spurious_interrupt_register
                .write(flags.bits() | vec as u32)
        }
    }

    // Reserve a 4K chunk of memory -- we don't really care where, we only care that we don't
    // overlap and can change the physical address it points to.
    static mut APIC_MMIO_AREA: MaybeUninit<ApicRegisters> = MaybeUninit::uninit();

    pub(crate) fn init(apic_base: PhysAddr) -> &'static mut ApicRegisters {
        // Remap APIC_MMIO_AREA to be backed by `apic_base`. We expect APIC_MMIO_AREA virtual
        // address to be somewhere in the first two megabytes.

        // Safety: we're not dereferencing the pointer, we just want to know where it landed in
        // virtual memory.
        let vaddr = VirtAddr::from_ptr(unsafe { APIC_MMIO_AREA.as_ptr() });
        if vaddr.as_u64() > Size2MiB::SIZE {
            panic!("APIC_MMIO_AREA virtual address does not land in the first page table");
        }
        let mut tables = PAGE_TABLE_REFS.get().unwrap().lock();
        tables.pt_0[vaddr.p1_index()].set_addr(
            apic_base,
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_CACHE,
        );
        flush_all();
        // Safety: we've mapped APIC_MMIO_AREA to where the caller claimed it to be.
        unsafe { APIC_MMIO_AREA.assume_init_mut() }
    }
}

mod x2apic {
    use x86_64::registers::model_specific::Msr;

    use super::{ApicErrorFlags, SpuriousInterruptFlags};

    pub(crate) const APIC_ID_REGISTER: X2ApicIdRegister = X2ApicIdRegister(Msr::new(0x0000_00802));
    pub(crate) const APIC_VERSION_REGISTER: ApicVersionRegister =
        ApicVersionRegister(Msr::new(0x0000_00803));
    pub(crate) const ERROR_STATUS_REGISTER: ErrorStatusRegister =
        ErrorStatusRegister(Msr::new(0x0000_00828));
    pub(crate) const INTERRUPT_COMMAND_REGISTER: InterruptCommandRegister =
        InterruptCommandRegister(Msr::new(0x0000_00830));
    pub(crate) const SPURIOUS_INTERRUPT_REGISTER: SpuriousInterruptRegister =
        SpuriousInterruptRegister(Msr::new(0x0000_00830));

    /// The x2APIC_ID register.
    ///
    /// Contains the 32-bit local x2APIC ID. It is assigned by hardware at reset time, and the exact
    /// structure is manufacturer-dependent.
    ///
    /// See Section 16.12 (x2APIC_ID) in the AMD64 Architecture Programmer's Manual, Volume 2 for
    /// more details.
    pub(crate) struct X2ApicIdRegister(Msr);

    impl super::ApicId for X2ApicIdRegister {
        fn apic_id(&self) -> u32 {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { self.0.read() as u32 }
        }
    }

    pub(crate) struct InterruptCommandRegister(Msr);

    impl super::InterprocessorInterrupt for InterruptCommandRegister {
        fn send(
            &mut self,
            destination: u32,
            vector: u8,
            message_type: super::MessageType,
            destination_mode: super::DestinationMode,
            level: super::Level,
            trigger_mode: super::TriggerMode,
            destination_shorthand: super::DestinationShorthand,
        ) -> Result<(), &'static str> {
            let mut value: u64 = (destination as u64) << 32;
            value |= (destination_shorthand as u64) << 18;
            value |= (trigger_mode as u64) << 15;
            value |= (level as u64) << 14;
            value |= (destination_mode as u64) << 11;
            value |= (message_type as u64) << 8;
            value |= vector as u64;
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { self.0.write(value) };
            Ok(())
        }
    }

    pub(crate) struct ErrorStatusRegister(Msr);

    impl super::ErrorStatus for ErrorStatusRegister {
        fn read(&self) -> ApicErrorFlags {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            ApicErrorFlags::from_bits_truncate(unsafe { self.0.read() }.try_into().unwrap())
        }
        fn clear(&mut self) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { self.0.write(0) }
        }
    }

    pub(crate) struct ApicVersionRegister(Msr);

    impl super::ApicVersion for ApicVersionRegister {
        fn read(&self) -> (bool, u8, u8) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            let val = unsafe { self.0.read() };

            (
                val & (1 << 31) > 0,            // EAS
                ((val & 0xFF0000) >> 16) as u8, // MLE
                (val & 0xFF) as u8,             // VER
            )
        }
    }

    pub(crate) struct SpuriousInterruptRegister(Msr);

    impl super::SpuriousInterrupts for SpuriousInterruptRegister {
        fn read(&self) -> (SpuriousInterruptFlags, u8) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            let val = unsafe { self.0.read() } as u32;

            (
                SpuriousInterruptFlags::from_bits_truncate(val),
                (val & 0xFF) as u8,
            )
        }

        fn write(&mut self, flags: SpuriousInterruptFlags, vec: u8) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { self.0.write(flags.bits() as u64 | vec as u64) };
        }
    }
}

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
        let aba = PhysAddr::new(val & 0x000F_FFFF_FFFF_F000u64);
        let flags = ApicBaseFlags::from_bits_truncate(val);

        (aba, flags)
    }

    pub fn write(aba: PhysAddr, flags: ApicBaseFlags) {
        Self::write_raw(flags.bits() | aba.as_u64());
    }
}

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

enum Apic {
    Xapic(&'static mut xapic::ApicRegisters),
    X2apic(
        x2apic::InterruptCommandRegister,
        x2apic::ErrorStatusRegister,
        x2apic::ApicVersionRegister,
        x2apic::SpuriousInterruptRegister,
    ),
}

/// Wrapper for the local APIC.
///
/// Currenty only supports x2APIC mode.
pub struct Lapic {
    apic_id: u32,
    interface: Apic,
}

impl Lapic {
    pub fn enable() -> Result<Self, &'static str> {
        // Safety: the CPUs we support are new enough to support CPUID.
        let result = unsafe { __cpuid(0x0000_0001) };
        let x2apic = result.ecx & (1 << 21) > 0;
        // See Section 16.9 in the AMD64 Architecture Programmer's Manual, Volume 2 for explanation
        // of the initialization procedure.
        let (aba, mut flags) = ApicBase::read();
        if !flags.contains(ApicBaseFlags::AE) {
            flags |= ApicBaseFlags::AE;
            ApicBase::write(aba, flags);
        }
        if x2apic && !flags.contains(ApicBaseFlags::EXTD) {
            // Enable x2APIC, if available.
            flags |= ApicBaseFlags::EXTD;
            ApicBase::write(aba, flags);
        }

        let mut apic = if x2apic {
            log::info!("Using x2APIC for AP initialization.");
            Lapic {
                apic_id: x2apic::APIC_ID_REGISTER.apic_id(),
                interface: Apic::X2apic(
                    x2apic::INTERRUPT_COMMAND_REGISTER,
                    x2apic::ERROR_STATUS_REGISTER,
                    x2apic::APIC_VERSION_REGISTER,
                    x2apic::SPURIOUS_INTERRUPT_REGISTER,
                ),
            }
        } else {
            log::info!("Using xAPIC for AP initialization.");
            let apic = xapic::init(aba);
            Lapic {
                apic_id: apic.apic_id(),
                interface: Apic::Xapic(apic),
            }
        };
        // Version should be between [0x10...0x20).
        let (_, _, version) = apic.apic_version().read();
        if !(0x10..0x20).contains(&version) {
            log::warn!("LAPIC version: {:x}", version);
            return Err("LAPIC version not in valid range");
        }
        let (flags, vec) = apic.spurious_interrupt_register().read();
        if !flags.contains(SpuriousInterruptFlags::ASE) {
            apic.spurious_interrupt_register()
                .write(flags | SpuriousInterruptFlags::ASE, vec)
        }
        Ok(apic)
    }

    fn error_status(&mut self) -> &mut dyn ErrorStatus {
        match &mut self.interface {
            Apic::Xapic(regs) => *regs,
            Apic::X2apic(_, ref mut err, _, _) => err,
        }
    }

    fn interrupt_command(&mut self) -> &mut dyn InterprocessorInterrupt {
        match &mut self.interface {
            Apic::Xapic(regs) => *regs,
            Apic::X2apic(ref mut icr, _, _, _) => icr,
        }
    }

    fn apic_version(&mut self) -> &mut dyn ApicVersion {
        match &mut self.interface {
            Apic::Xapic(regs) => *regs,
            Apic::X2apic(_, _, ver, _) => ver,
        }
    }

    fn spurious_interrupt_register(&mut self) -> &mut dyn SpuriousInterrupts {
        match &mut self.interface {
            Apic::Xapic(regs) => *regs,
            Apic::X2apic(_, _, _, spi) => spi,
        }
    }

    /// Sends an INIT IPI to the local APIC specified by `destination`.
    pub fn send_init_ipi(&mut self, destination: u32) -> Result<(), &'static str> {
        self.error_status().clear();
        self.interrupt_command().send(
            destination,
            0,
            MessageType::Init,
            DestinationMode::Physical,
            Level::Assert,
            TriggerMode::Level,
            DestinationShorthand::DestinationField,
        )?;
        self.interrupt_command().send(
            destination,
            0,
            MessageType::Init,
            DestinationMode::Physical,
            Level::Deassert,
            TriggerMode::Edge,
            DestinationShorthand::DestinationField,
        )
    }

    /// Sends a STARTUP IPI (SIPI) to the local APIC specified by `destination`.
    pub fn send_startup_ipi(
        &mut self,
        destination: u32,
        vector: PhysAddr,
    ) -> Result<(), &'static str> {
        if !vector.is_aligned(0x1000u64) {
            return Err("startup vector is not page-aligned");
        }
        let vector = vector.as_u64();
        if vector > 0x100000 {
            return Err("startup vector needs to be in the first megabyte of memory");
        }
        self.error_status().clear();
        self.interrupt_command().send(
            destination,
            (vector / 0x1000) as u8,
            MessageType::Startup,
            DestinationMode::Physical,
            Level::Assert,
            TriggerMode::Level,
            DestinationShorthand::DestinationField,
        )
    }

    pub fn local_apic_id(&self) -> u32 {
        self.apic_id
    }
}
