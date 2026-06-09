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

use core::arch::x86_64::CpuidResult;

pub mod mmio;
use log::error;
pub use mmio::SevMmio;
use oak_core::sync::OnceCell;
use oak_hal::{PageAssignment, PageEncryption, Platform, PortFactory};
use oak_restricted_kernel::{PAGE_TABLES, Translator, shutdown};
use oak_sev_guest::{
    interrupts::{MutableInterruptStackFrame, mutable_interrupt_handler_with_error_code},
    msr::{
        SevStatus, TerminationReason, TerminationRequest, get_cpuid_for_vc_exception,
        get_sev_status, request_termination,
    },
};
use x86_64::structures::{
    mem_encrypt::{MemoryEncryptionConfiguration, enable_memory_encryption},
    paging::{Page, PhysFrame, Size4KiB},
    port::{PortRead, PortWrite},
};

use crate::snp::{CPUID_PAGE, get_snp_page_addresses, init_snp_pages};

static SEV_STATUS: OnceCell<SevStatus> = OnceCell::new();

/// For now we use a fixed position for the encrypted bit. For now we assume
/// that we will be running on AMD Arcadia-Milan CPUs, which use bit 51.
pub const ENCRYPTED_BIT_POSITION: u8 = 51;

fn sev_status() -> SevStatus {
    *SEV_STATUS.get().expect("SEV status not set")
}

pub struct Sev {}

impl Platform for Sev {
    type Mmio = SevMmio;

    fn init_memory_encryption() -> bool {
        if get_sev_status().unwrap_or(SevStatus::empty()).contains(SevStatus::SEV_ENABLED) {
            unsafe {
                enable_memory_encryption(MemoryEncryptionConfiguration::EncryptedBit(
                    ENCRYPTED_BIT_POSITION,
                ));
            }
            true
        } else {
            false
        }
    }

    fn cpuid(_leaf: u32) -> CpuidResult {
        todo!();
    }

    /// # Safety
    ///
    /// The caller must ensure that the base address and the size represents a
    /// valid MMIO region.
    unsafe fn mmio(base_address: x86_64::PhysAddr, size: usize) -> Self::Mmio {
        let base_virt = PAGE_TABLES.lock().get().unwrap().translate_physical(base_address).unwrap();
        let use_ghcb = crate::ghcb::GHCB_PROTOCOL.get().is_some();

        // Safety: The caller must ensure that the physical MMIO base address and size
        // are valid. We translated the caller-provided base address to a valid
        // virtual address using the current valid page tables.
        unsafe { SevMmio::new(base_virt, base_address, size, use_ghcb) }
    }

    fn port_factory() -> PortFactory {
        if crate::ghcb::GHCB_PROTOCOL.get().is_some() {
            PortFactory {
                read_u8: |port| crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_read_u8(port),
                read_u16: |port| crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_read_u16(port),
                read_u32: |port| crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_read_u32(port),
                write_u8: |port, value| {
                    crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_write_u8(port, value)
                },
                write_u16: |port, value| {
                    crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_write_u16(port, value)
                },
                write_u32: |port, value| {
                    crate::ghcb::GHCB_PROTOCOL.get().unwrap().lock().io_write_u32(port, value)
                },
            }
        } else {
            // Fall back to direct port-based I/O when not running under
            // SEV-ES or SEV-SNP.
            PortFactory {
                read_u8: |port| unsafe { Ok(u8::read_from_port(port)) },
                read_u16: |port| unsafe { Ok(u16::read_from_port(port)) },
                read_u32: |port| unsafe { Ok(u32::read_from_port(port)) },
                write_u8: |port, value| {
                    unsafe { u8::write_to_port(port, value) };
                    Ok(())
                },
                write_u16: |port, value| {
                    unsafe { u16::write_to_port(port, value) };
                    Ok(())
                },
                write_u32: |port, value| {
                    unsafe { u32::write_to_port(port, value) };
                    Ok(())
                },
            }
        }
    }

    fn early_initialize_platform() {
        SEV_STATUS
            .set(get_sev_status().unwrap_or(SevStatus::empty()))
            .expect("SEV status already set");
        if sev_status().contains(SevStatus::SEV_ES_ENABLED) {
            crate::ghcb::init(sev_status().contains(SevStatus::SNP_ACTIVE));
        }
    }

    fn change_frame_state(frame: PhysFrame<Size4KiB>, state: PageAssignment) {
        if sev_status().contains(SevStatus::SNP_ACTIVE) {
            let page_gpa = frame.start_address().as_u64() as usize;

            let assignment = match state {
                PageAssignment::Shared => oak_sev_guest::msr::PageAssignment::Shared,
                PageAssignment::Private => oak_sev_guest::msr::PageAssignment::Private,
            };

            let request = oak_sev_guest::msr::SnpPageStateChangeRequest::new(page_gpa, assignment)
                .expect("failed to create SNP page state change request");

            oak_sev_guest::msr::change_snp_page_state(request)
                .expect("failed to change SNP page state");
        }
    }

    fn revalidate_page(_page: Page<Size4KiB>) {
        todo!();
    }

    fn page_table_mask(_encryption_state: PageEncryption) -> u64 {
        todo!();
    }

    fn encrypted() -> u64 {
        todo!();
    }

    fn wbvind() {
        todo!();
    }
}

impl oak_hal::MsrAccess for Sev {
    unsafe fn read_msr(_msr: u32) -> u64 {
        todo!();
    }

    unsafe fn write_msr(_msr: u32, _value: u64) {
        todo!();
    }
}

mutable_interrupt_handler_with_error_code!(
    unsafe fn vmm_communication_exception_handler(
        stack_frame: &mut MutableInterruptStackFrame,
        error_code: u64,
    ) {
        match error_code {
            0x72 => {
                // Make sure it was triggered from a CPUID instruction.
                const CPUID_INSTRUCTION: u16 = 0xa20f;
                // Safety: we are copying two bytes and interpreting it as a
                // 16-bit number without making any other assumptions about
                // the layout.
                let instruction: u16 =
                    unsafe { core::ptr::read_unaligned(stack_frame.rip.as_ptr()) };
                if instruction != CPUID_INSTRUCTION {
                    panic!("INSTRUCTION WAS NOT CPUID");
                }

                if let Some(cpuid_page) = CPUID_PAGE.get() {
                    let target = stack_frame.into();
                    let count = cpuid_page.count as usize;
                    if let Some(found) =
                        cpuid_page.cpuid_data[0..count].iter().find(|item| item.input == target)
                    {
                        stack_frame.rax = found.output.eax as u64;
                        stack_frame.rbx = found.output.ebx as u64;
                        stack_frame.rcx = found.output.ecx as u64;
                        stack_frame.rdx = found.output.edx as u64;
                    } else {
                        // For now we just log the error so that we can see when this happens.
                        // TODO(#3470): Improve handling of incorrect/missing CPUID requests.
                        error!("KERNEL PANIC: REQUESTED CPUID NOT PRESENT IN CPUID PAGE");
                        error!("Instruction pointer: {:#016x}", stack_frame.rip.as_u64());
                        error!("RAX: {:#016x}", stack_frame.rax);
                        error!("RCX: {:#016x}", stack_frame.rcx);
                        shutdown::shutdown();
                    }
                } else {
                    let leaf = stack_frame.rax as u32;
                    // The MSR protocol does not support sub-leaf requests or leaf 0x0000_000D.
                    // See section 2.3.1 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>
                    // TODO(#3470): Improve handling of incorrect/missing CPUID requests.
                    if stack_frame.rcx != 0 || leaf == 0x0000_000D {
                        error!("KERNEL PANIC: CPUID SUB-LEAF OR INVALID LEAD REQUESTED");
                        error!("Instruction pointer: {:#016x}", stack_frame.rip.as_u64());
                        error!("RAX: {:#016x}", stack_frame.rax);
                        error!("RCX: {:#016x}", stack_frame.rcx);
                        shutdown::shutdown();
                    }
                    get_cpuid_for_vc_exception(leaf, stack_frame).expect("error reading CPUID");
                }
                // CPUID instruction is 2 bytes long, so we advance the instruction pointer by
                // 2.
                stack_frame.rip += 2u64;
            }
            _ => {
                error!("KERNEL PANIC: UNHANDLED #VC EXCEPTION");
                error!("Instruction pointer: {:#016x}", stack_frame.rip.as_u64());
                error!("Error code: {:#x}", error_code);
                shutdown::shutdown();
            }
        }
    }
);

impl oak_restricted_kernel::hal::KernelPlatform for Sev {
    fn initialize_platform(info: &oak_linux_boot_params::BootParams) {
        let sev_status = sev_status();
        if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
            let mut pt_guard = PAGE_TABLES.lock();
            let mapper = pt_guard.get_mut().unwrap();
            // Now that the page tables have been updated, we have to re-share the GHCB with
            // the hypervisor.
            crate::ghcb::reshare_ghcb(mapper);
            if sev_status.contains(SevStatus::SNP_ACTIVE) {
                // We must also initialise the CPUID and secrets pages and the guest message
                // encryptor when SEV-SNP is active. Panicking is OK at this point,
                // because these pages are required to support the full features and
                // we don't want to run without them.
                init_snp_pages(get_snp_page_addresses(info, mapper), mapper);
            }
        }
    }

    fn add_additional_interrupt_handlers(
        idt: &mut x86_64::structures::idt::InterruptDescriptorTable,
    ) {
        let vc_handler_address =
            x86_64::VirtAddr::new(vmm_communication_exception_handler as *const () as usize as u64);
        // Safety: we are passing a valid address of a function with the correct
        // signature.
        unsafe {
            idt.vmm_communication_exception.set_handler_addr(vc_handler_address); // vector 29
        }
    }

    fn shutdown() -> ! {
        let sev_status = sev_status();
        if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
            request_termination(TerminationRequest { reason: TerminationReason::General });
        }
        shutdown::shutdown_with_port_factory(&Self::port_factory())
    }
}
