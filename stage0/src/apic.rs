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

use x86_64::{PhysAddr, structures::paging::Size4KiB};

use crate::{
    Platform,
    msr::{
        ApicBase, ApicBaseFlags, ApicErrorFlags, DestinationMode, DestinationShorthand, Level,
        MessageType, SpuriousInterruptFlags, TriggerMode, X2ApicErrorStatusRegister,
        X2ApicIdRegister, X2ApicInterruptCommandRegister, X2ApicSpuriousInterruptRegister,
        X2ApicVersionRegister,
    },
};

/// Interrupt Command.
///
/// Used to send inter-processor interrupts (IPIs) to other cores in the system.
///
/// See Section 16.5 (Interprocessor Interrupts) and Section 16/13 (x2APIC
/// Interrupt Command Register Operations) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
trait InterprocessorInterrupt<P: Platform> {
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
/// See Section 16.4.6 (APIC Error Interrupts) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
trait ErrorStatus<P: Platform> {
    #[allow(unused)]
    fn read(&self) -> ApicErrorFlags;
    fn clear(&mut self);
}

/// LAPIC identifier.
///
/// For APIC, it's 4 bits; xAPIC, 8 bits; x2APIC, 32 bits.
trait ApicId {
    fn apic_id<P: Platform>(&self) -> u32;
}

/// APIC Version.
///
/// See Section 16.3.4 (APIC Version Register) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
trait ApicVersion<P> {
    fn read(&self) -> (bool, u8, u8);
}

/// APIC spurious interrupt register.
///
/// See Section 16.4.7 (Spurious Interrupts) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
trait SpuriousInterrupts<P> {
    fn read(&self) -> (SpuriousInterruptFlags, u8);
    fn write(&mut self, flags: SpuriousInterruptFlags, vec: u8);
}

mod xapic {
    use x86_64::{PhysAddr, structures::paging::Size4KiB};

    use super::{ApicErrorFlags, SpuriousInterruptFlags};
    use crate::{Platform, hal};

    // We divide the offset by 4 as we're indexing by u32's, not bytes.
    const APIC_ID_REGISTER_OFFSET: usize = 0x020 / core::mem::size_of::<u32>();
    const APIC_VERSION_REGISTER_OFFSET: usize = 0x30 / core::mem::size_of::<u32>();
    const SPURIOUS_INTERRUPT_REGISTER_OFFSET: usize = 0x0F0 / core::mem::size_of::<u32>();
    const ERROR_STATUS_REGISTER_OFFSET: usize = 0x280 / core::mem::size_of::<u32>();
    const INTERRUPT_COMMAND_REGISTER_LOW_OFFSET: usize = 0x300 / core::mem::size_of::<u32>();
    const INTERRUPT_COMMAND_REGISTER_HIGH_OFFSET: usize = 0x310 / core::mem::size_of::<u32>();

    pub(crate) struct Xapic<M: hal::Mmio<Size4KiB>> {
        mmio: M,
    }

    impl<M: hal::Mmio<Size4KiB>> Xapic<M> {
        fn read(&self, register: usize) -> u32 {
            self.mmio.read_u32(register)
        }
        unsafe fn write(&mut self, register: usize, val: u32) {
            unsafe { self.mmio.write_u32(register, val) }
        }
    }

    impl<M: hal::Mmio<Size4KiB>> super::ApicId for Xapic<M> {
        /// Read the Local APIC ID register.
        ///
        /// See Section 16.3.3 in the AMD64 Architecture Programmer's Manual,
        /// Volume 2 for the register format.
        fn apic_id<P: Platform>(&self) -> u32 {
            self.read(APIC_ID_REGISTER_OFFSET) >> 24
        }
    }

    impl<P: Platform> super::InterprocessorInterrupt<P> for Xapic<P::Mmio<Size4KiB>> {
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
            let destination: u8 =
                destination.try_into().map_err(|_| "destination APIC ID too big for xAPIC")?;
            // Safety: the values we write are valid according to the spec.
            unsafe {
                self.write(INTERRUPT_COMMAND_REGISTER_HIGH_OFFSET, (destination as u32) << 24);
                self.write(
                    INTERRUPT_COMMAND_REGISTER_LOW_OFFSET,
                    destination_shorthand as u32
                        | trigger_mode as u32
                        | level as u32
                        | destination_mode as u32
                        | message_type as u32
                        | vector as u32,
                );
            }
            Ok(())
        }
    }

    impl<P: Platform> super::ErrorStatus<P> for Xapic<P::Mmio<Size4KiB>> {
        fn read(&self) -> ApicErrorFlags {
            ApicErrorFlags::from_bits_truncate(self.read(ERROR_STATUS_REGISTER_OFFSET))
        }

        fn clear(&mut self) {
            // Safety: zeroing the register is valid for ErrorStatus.
            unsafe { self.write(ERROR_STATUS_REGISTER_OFFSET, 0) }
        }
    }

    impl<P: Platform> super::ApicVersion<P> for Xapic<P::Mmio<Size4KiB>> {
        fn read(&self) -> (bool, u8, u8) {
            let val = self.read(APIC_VERSION_REGISTER_OFFSET);

            (
                val & (1 << 31) > 0,            // EAS
                ((val & 0xFF0000) >> 16) as u8, // MLE
                (val & 0xFF) as u8,             // VER
            )
        }
    }

    impl<P: Platform> super::SpuriousInterrupts<P> for Xapic<P::Mmio<Size4KiB>> {
        fn read(&self) -> (SpuriousInterruptFlags, u8) {
            let val = self.read(SPURIOUS_INTERRUPT_REGISTER_OFFSET);

            (SpuriousInterruptFlags::from_bits_truncate(val), (val & 0xFF) as u8)
        }

        fn write(&mut self, flags: super::SpuriousInterruptFlags, vec: u8) {
            // Safety: the values we write are valid according to the spec.
            unsafe { self.write(SPURIOUS_INTERRUPT_REGISTER_OFFSET, flags.bits() | vec as u32) }
        }
    }

    /// Safety: caller needs to guarantee that `apic_base` points to the APIC
    /// MMIO memory.
    pub(crate) unsafe fn init<P: Platform>(apic_base: PhysAddr) -> Xapic<P::Mmio<Size4KiB>> {
        Xapic { mmio: unsafe { P::mmio::<Size4KiB>(apic_base) } }
    }
}

mod x2apic {
    use super::{ApicErrorFlags, SpuriousInterruptFlags};
    use crate::{
        Platform,
        msr::{
            X2ApicErrorStatusRegister, X2ApicIdRegister, X2ApicInterruptCommandRegister,
            X2ApicSpuriousInterruptRegister, X2ApicVersionRegister,
        },
    };

    impl super::ApicId for X2ApicIdRegister {
        fn apic_id<P: Platform>(&self) -> u32 {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::apic_id::<P>() }
        }
    }

    impl<P: Platform> super::InterprocessorInterrupt<P> for X2ApicInterruptCommandRegister {
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
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe {
                Self::send::<P>(
                    vector,
                    message_type,
                    destination_mode,
                    level,
                    trigger_mode,
                    destination_shorthand,
                    destination,
                )
            }
            Ok(())
        }
    }

    impl<P: Platform> super::ErrorStatus<P> for X2ApicErrorStatusRegister {
        fn read(&self) -> ApicErrorFlags {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::read::<P>() }
        }
        fn clear(&mut self) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::clear::<P>() }
        }
    }

    impl<P: Platform> super::ApicVersion<P> for X2ApicVersionRegister {
        fn read(&self) -> (bool, u8, u8) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::read::<P>() }
        }
    }

    impl<P: Platform> super::SpuriousInterrupts<P> for X2ApicSpuriousInterruptRegister {
        fn read(&self) -> (SpuriousInterruptFlags, u8) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::read::<P>() }
        }

        fn write(&mut self, flags: SpuriousInterruptFlags, vec: u8) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::write::<P>(flags, vec) };
        }
    }
}

enum Apic<M: crate::hal::Mmio<Size4KiB>> {
    Xapic(xapic::Xapic<M>),
    X2apic(
        X2ApicInterruptCommandRegister,
        X2ApicErrorStatusRegister,
        X2ApicVersionRegister,
        X2ApicSpuriousInterruptRegister,
    ),
}

/// Wrapper for the local APIC.
///
/// Currenty only supports x2APIC mode.
pub struct Lapic<M: crate::hal::Mmio<Size4KiB>> {
    apic_id: u32,
    interface: Apic<M>,
}

impl<M: crate::hal::Mmio<Size4KiB>> Lapic<M> {
    pub fn enable<P: Platform<Mmio<Size4KiB> = M>>() -> Result<Self, &'static str> {
        let x2apic = P::cpuid(0x0000_0001).ecx & (1 << 21) > 0;
        // See Section 16.9 in the AMD64 Architecture Programmer's Manual, Volume 2 for
        // explanation of the initialization procedure.
        let (aba, mut flags) = ApicBase::read::<P>();
        if !flags.contains(ApicBaseFlags::AE) {
            flags |= ApicBaseFlags::AE;
            ApicBase::write::<P>(aba, flags);
        }
        if x2apic && !flags.contains(ApicBaseFlags::EXTD) {
            // Enable x2APIC, if available.
            flags |= ApicBaseFlags::EXTD;
            ApicBase::write::<P>(aba, flags);
        }

        let mut apic = if x2apic {
            log::info!("Using x2APIC for AP initialization.");
            Lapic {
                apic_id: unsafe { X2ApicIdRegister::apic_id::<P>() },
                interface: Apic::X2apic(
                    X2ApicInterruptCommandRegister,
                    X2ApicErrorStatusRegister,
                    X2ApicVersionRegister,
                    X2ApicSpuriousInterruptRegister,
                ),
            }
        } else {
            log::info!("Using xAPIC for AP initialization.");
            // Safety: we trust the address provided by the ApicBase MSR.
            let apic = unsafe { xapic::init::<P>(aba) };
            Lapic { apic_id: apic.apic_id::<P>(), interface: Apic::Xapic(apic) }
        };
        // Version should be between [0x10...0x20).
        let (_, _, version) = apic.apic_version::<P>().read();
        if !(0x10..0x20).contains(&version) {
            log::warn!("LAPIC version: {:x}", version);
            return Err("LAPIC version not in valid range");
        }
        let (flags, vec) = apic.spurious_interrupt_register::<P>().read();
        if !flags.contains(SpuriousInterruptFlags::ASE) {
            apic.spurious_interrupt_register::<P>().write(flags | SpuriousInterruptFlags::ASE, vec)
        }
        Ok(apic)
    }

    fn error_status<P: Platform<Mmio<Size4KiB> = M>>(&mut self) -> &mut dyn ErrorStatus<P> {
        match &mut self.interface {
            Apic::Xapic(regs) => regs,
            Apic::X2apic(_, err, _, _) => err,
        }
    }

    fn interrupt_command<P: Platform<Mmio<Size4KiB> = M>>(
        &mut self,
    ) -> &mut dyn InterprocessorInterrupt<P> {
        match &mut self.interface {
            Apic::Xapic(regs) => regs,
            Apic::X2apic(icr, _, _, _) => icr,
        }
    }

    fn apic_version<P: Platform<Mmio<Size4KiB> = M>>(&mut self) -> &mut dyn ApicVersion<P> {
        match &mut self.interface {
            Apic::Xapic(regs) => regs,
            Apic::X2apic(_, _, ver, _) => ver,
        }
    }

    fn spurious_interrupt_register<P: Platform<Mmio<Size4KiB> = M>>(
        &mut self,
    ) -> &mut dyn SpuriousInterrupts<P> {
        match &mut self.interface {
            Apic::Xapic(regs) => regs,
            Apic::X2apic(_, _, _, spi) => spi,
        }
    }

    /// Sends an INIT IPI to the local APIC specified by `destination`.
    pub fn send_init_ipi<P: Platform<Mmio<Size4KiB> = M>>(
        &mut self,
        destination: u32,
    ) -> Result<(), &'static str> {
        self.error_status::<P>().clear();
        self.interrupt_command::<P>().send(
            destination,
            0,
            MessageType::Init,
            DestinationMode::Physical,
            Level::Assert,
            TriggerMode::Level,
            DestinationShorthand::DestinationField,
        )?;
        self.interrupt_command::<P>().send(
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
    pub fn send_startup_ipi<P: Platform<Mmio<Size4KiB> = M>>(
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
        self.error_status::<P>().clear();
        self.interrupt_command::<P>().send(
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
