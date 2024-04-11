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

use oak_sev_guest::cpuid::CpuidInput;
use x86_64::PhysAddr;

use crate::{
    msr::{
        ApicBase, ApicBaseFlags, ApicErrorFlags, DestinationMode, DestinationShorthand, Level,
        MessageType, SpuriousInterruptFlags, TriggerMode, X2ApicErrorStatusRegister,
        X2ApicIdRegister, X2ApicInterruptCommandRegister, X2ApicSpuriousInterruptRegister,
        X2ApicVersionRegister,
    },
    sev::GHCB_WRAPPER,
};

/// Interrupt Command.
///
/// Used to send inter-processor interrupts (IPIs) to other cores in the system.
///
/// See Section 16.5 (Interprocessor Interrupts) and Section 16/13 (x2APIC
/// Interrupt Command Register Operations) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
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
/// See Section 16.4.6 (APIC Error Interrupts) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
trait ErrorStatus {
    #[allow(unused)]
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
/// See Section 16.3.4 (APIC Version Register) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
trait ApicVersion {
    fn read(&self) -> (bool, u8, u8);
}

/// APIC spurious interrupt register.
///
/// See Section 16.4.7 (Spurious Interrupts) in the AMD64 Architecture
/// Programmer's Manual, Volume 2 for more details.
trait SpuriousInterrupts {
    fn read(&self) -> (SpuriousInterruptFlags, u8);
    fn write(&mut self, flags: SpuriousInterruptFlags, vec: u8);
}

mod xapic {
    use core::mem::MaybeUninit;

    use x86_64::{
        instructions::tlb::flush_all,
        structures::paging::{PageSize, PageTableFlags, Size2MiB, Size4KiB},
        PhysAddr, VirtAddr,
    };

    use super::{ApicErrorFlags, SpuriousInterruptFlags};
    use crate::{paging::PAGE_TABLE_REFS, sev::GHCB_WRAPPER};

    /// Representation of the APIC MMIO registers.
    ///
    /// We do not represent _all_ the xAPIC registers here, but only the ones we
    /// are interested in.
    ///
    /// The exact layout is defined in Table 16-2 and Section 16.3.2 (APIC
    /// Registers) of the AMD64 Architecture Programmer's Manual, Volume 2.
    #[repr(C, align(4096))]
    struct ApicRegisters {
        registers: [u32; 1024],
    }
    static_assertions::assert_eq_size!(ApicRegisters, [u8; Size4KiB::SIZE as usize]);

    // We divide the offset by 4 as we're indexing by u32's, not bytes.
    const APIC_ID_REGISTER_OFFSET: usize = 0x020 / core::mem::size_of::<u32>();
    const APIC_VERSION_REGISTER_OFFSET: usize = 0x30 / core::mem::size_of::<u32>();
    const SPURIOUS_INTERRUPT_REGISTER_OFFSET: usize = 0x0F0 / core::mem::size_of::<u32>();
    const ERROR_STATUS_REGISTER_OFFSET: usize = 0x280 / core::mem::size_of::<u32>();
    const INTERRUPT_COMMAND_REGISTER_LOW_OFFSET: usize = 0x300 / core::mem::size_of::<u32>();
    const INTERRUPT_COMMAND_REGISTER_HIGH_OFFSET: usize = 0x310 / core::mem::size_of::<u32>();

    pub(crate) struct Xapic {
        mmio_area: &'static mut ApicRegisters,

        // APIC base address, we keep track of it as we may need to use the GHCB protocol instead
        // of accessing `mmio_area` directly
        aba: PhysAddr,
    }

    impl Xapic {
        fn read(&self, register: usize) -> u32 {
            // Safety: these registers can only be accessed through ApicRegisters, by which
            // we should have established where the MMIO area is.
            if let Some(ghcb) = GHCB_WRAPPER.get() {
                ghcb.lock()
                    .mmio_read_u32(self.aba + (register * core::mem::size_of::<u32>()))
                    .expect("couldn't read the MSR using the GHCB protocol")
            } else {
                // Safety: the APIC base register is supported in all modern CPUs.
                unsafe { (&self.mmio_area.registers[register] as *const u32).read_volatile() }
            }
        }
        fn write(&mut self, register: usize, val: u32) {
            if let Some(ghcb) = GHCB_WRAPPER.get() {
                ghcb.lock()
                    .mmio_write_u32(self.aba + (register * core::mem::size_of::<u32>()), val)
                    .expect("couldn't read the MSR using the GHCB protocol")
            } else {
                // Safety: these registers can only be accessed through ApicRegisters, by which
                // we should have established where the MMIO area is.
                unsafe { (&mut self.mmio_area.registers[register] as *mut u32).write_volatile(val) }
            }
        }
    }

    impl super::ApicId for Xapic {
        /// Read the Local APIC ID register.
        ///
        /// See Section 16.3.3 in the AMD64 Architecture Programmer's Manual,
        /// Volume 2 for the register format.
        fn apic_id(&self) -> u32 {
            self.read(APIC_ID_REGISTER_OFFSET) >> 24
        }
    }

    impl super::InterprocessorInterrupt for Xapic {
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
            Ok(())
        }
    }

    impl super::ErrorStatus for Xapic {
        fn read(&self) -> ApicErrorFlags {
            ApicErrorFlags::from_bits_truncate(self.read(ERROR_STATUS_REGISTER_OFFSET))
        }

        fn clear(&mut self) {
            self.write(ERROR_STATUS_REGISTER_OFFSET, 0)
        }
    }

    impl super::ApicVersion for Xapic {
        fn read(&self) -> (bool, u8, u8) {
            let val = self.read(APIC_VERSION_REGISTER_OFFSET);

            (
                val & (1 << 31) > 0,            // EAS
                ((val & 0xFF0000) >> 16) as u8, // MLE
                (val & 0xFF) as u8,             // VER
            )
        }
    }

    impl super::SpuriousInterrupts for Xapic {
        fn read(&self) -> (SpuriousInterruptFlags, u8) {
            let val = self.read(SPURIOUS_INTERRUPT_REGISTER_OFFSET);

            (SpuriousInterruptFlags::from_bits_truncate(val), (val & 0xFF) as u8)
        }

        fn write(&mut self, flags: super::SpuriousInterruptFlags, vec: u8) {
            self.write(SPURIOUS_INTERRUPT_REGISTER_OFFSET, flags.bits() | vec as u32)
        }
    }

    // Reserve a 4K chunk of memory -- we don't really care where, we only care that
    // we don't overlap and can change the physical address it points to.
    static mut APIC_MMIO_AREA: MaybeUninit<ApicRegisters> = MaybeUninit::uninit();

    pub(crate) fn init(apic_base: PhysAddr) -> Xapic {
        // Remap APIC_MMIO_AREA to be backed by `apic_base`. We expect APIC_MMIO_AREA
        // virtual address to be somewhere in the first two megabytes.

        // Safety: we're not dereferencing the pointer, we just want to know where it
        // landed in virtual memory.
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
        Xapic { mmio_area: unsafe { APIC_MMIO_AREA.assume_init_mut() }, aba: apic_base }
    }
}

mod x2apic {
    use super::{ApicErrorFlags, SpuriousInterruptFlags};
    use crate::msr::{
        X2ApicErrorStatusRegister, X2ApicIdRegister, X2ApicInterruptCommandRegister,
        X2ApicSpuriousInterruptRegister, X2ApicVersionRegister,
    };

    impl super::ApicId for X2ApicIdRegister {
        fn apic_id(&self) -> u32 {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::apic_id() }
        }
    }

    impl super::InterprocessorInterrupt for X2ApicInterruptCommandRegister {
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
                Self::send(
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

    impl super::ErrorStatus for X2ApicErrorStatusRegister {
        fn read(&self) -> ApicErrorFlags {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::read() }
        }
        fn clear(&mut self) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::clear() }
        }
    }

    impl super::ApicVersion for X2ApicVersionRegister {
        fn read(&self) -> (bool, u8, u8) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::read() }
        }
    }

    impl super::SpuriousInterrupts for X2ApicSpuriousInterruptRegister {
        fn read(&self) -> (SpuriousInterruptFlags, u8) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::read() }
        }

        fn write(&mut self, flags: SpuriousInterruptFlags, vec: u8) {
            // Safety: we've estabished we're using x2APIC, so accessing the MSR is safe.
            unsafe { Self::write(flags, vec) };
        }
    }
}

enum Apic {
    Xapic(xapic::Xapic),
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
pub struct Lapic {
    apic_id: u32,
    interface: Apic,
}

impl Lapic {
    pub fn enable() -> Result<Self, &'static str> {
        let x2apic = if let Some(ghcb) = GHCB_WRAPPER.get() {
            ghcb.lock().get_cpuid(CpuidInput { eax: 0x0000_0001, ecx: 0, xcr0: 0, xss: 0 })?.ecx
        } else {
            // Safety: the CPUs we support are new enough to support CPUID.
            unsafe { __cpuid(0x0000_0001) }.ecx
        } & (1 << 21)
            > 0;
        // See Section 16.9 in the AMD64 Architecture Programmer's Manual, Volume 2 for
        // explanation of the initialization procedure.
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
                apic_id: unsafe { X2ApicIdRegister::apic_id() },
                interface: Apic::X2apic(
                    X2ApicInterruptCommandRegister,
                    X2ApicErrorStatusRegister,
                    X2ApicVersionRegister,
                    X2ApicSpuriousInterruptRegister,
                ),
            }
        } else {
            log::info!("Using xAPIC for AP initialization.");
            let apic = xapic::init(aba);
            Lapic { apic_id: apic.apic_id(), interface: Apic::Xapic(apic) }
        };
        // Version should be between [0x10...0x20).
        let (_, _, version) = apic.apic_version().read();
        if !(0x10..0x20).contains(&version) {
            log::warn!("LAPIC version: {:x}", version);
            return Err("LAPIC version not in valid range");
        }
        let (flags, vec) = apic.spurious_interrupt_register().read();
        if !flags.contains(SpuriousInterruptFlags::ASE) {
            apic.spurious_interrupt_register().write(flags | SpuriousInterruptFlags::ASE, vec)
        }
        Ok(apic)
    }

    fn error_status(&mut self) -> &mut dyn ErrorStatus {
        match &mut self.interface {
            Apic::Xapic(regs) => regs,
            Apic::X2apic(_, ref mut err, _, _) => err,
        }
    }

    fn interrupt_command(&mut self) -> &mut dyn InterprocessorInterrupt {
        match &mut self.interface {
            Apic::Xapic(regs) => regs,
            Apic::X2apic(ref mut icr, _, _, _) => icr,
        }
    }

    fn apic_version(&mut self) -> &mut dyn ApicVersion {
        match &mut self.interface {
            Apic::Xapic(regs) => regs,
            Apic::X2apic(_, _, ver, _) => ver,
        }
    }

    fn spurious_interrupt_register(&mut self) -> &mut dyn SpuriousInterrupts {
        match &mut self.interface {
            Apic::Xapic(regs) => regs,
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
