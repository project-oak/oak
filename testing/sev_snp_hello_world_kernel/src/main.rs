//
// Copyright 2022 The Project Oak Authors
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

#![no_std]
#![no_main]
#![feature(abi_x86_interrupt)]

use core::{arch::asm, ops::Deref, panic::PanicInfo};
use lazy_static::lazy_static;
use oak_linux_boot_params::{BootParams, CCBlobSevInfo, CCSetupData, SetupDataType};
use sev_guest::{
    cpuid::CpuidPage,
    msr::{get_sev_status, SevStatus},
    secrets::SecretsPage,
};
use x86_64::{
    instructions::{hlt, interrupts::int3},
    structures::idt::{InterruptDescriptorTable, InterruptStackFrame},
};

mod asm;
mod ghcb;
mod serial;

lazy_static! {
    static ref IDT: InterruptDescriptorTable = {
        let mut idt = InterruptDescriptorTable::new();
        idt.general_protection_fault.set_handler_fn(gp_handler);
        idt
    };
}

/// Crude implementation of a #GP handler that skips any `rdmsr` instructions that trigger #GP.
///
/// Note that this doesn't properly emulate reading the MSR! It doesn't change any register values;
/// the instruction is just skipped.
extern "x86-interrupt" fn gp_handler(mut frame: InterruptStackFrame, _: u64) {
    unsafe {
        // RDMSR can cause a #GP if you try to read a non-existing MSR
        if *frame.deref().instruction_pointer.as_ptr::<u16>() == 0x320Fu16 {
            // just skip the instruction
            frame.as_mut().update(|val| {
                val.instruction_pointer += 2u64;
            });
        } else {
            // not a RDMSR, trigger a double fault
            asm!("int 8", options(noreturn));
        }
    }
}

#[no_mangle]
pub extern "C" fn rust64_start(_: u64, boot_params: &BootParams) -> ! {
    IDT.load();
    serial::init_logging();
    log::info!("Hello World!");

    let sev_status = get_sev_status().unwrap_or(SevStatus::empty());
    if sev_status.contains(SevStatus::SEV_ENABLED) {
        log::info!("SEV enabled");
    }
    if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
        log::info!("SEV-ES enabled");
    }
    if sev_status.contains(SevStatus::SNP_ACTIVE) {
        log::info!("SNP active");

        // Walk the null-terminated setup_data list until we find the CC blob.
        let mut setup_data = boot_params.hdr.setup_data;

        // Safety: there's a lot of dereferences of raw pointers here; unfortunately necessary as we
        // need to access the C data structures set up by the bootloader. It is safe as long as the
        // bootloader populated the zero page correctly.
        while !setup_data.is_null() {
            let type_ = unsafe { (*setup_data).type_ };
            if type_ == SetupDataType::CCBlob {
                break;
            }
            setup_data = unsafe { (*setup_data).next };
        }

        if !setup_data.is_null() {
            let cc_setup_data = unsafe { &*(setup_data as *const CCSetupData) };
            let cc_blob = unsafe { &*(cc_setup_data.cc_blob_address as *const CCBlobSevInfo) };
            let magic = cc_blob.magic;
            if magic != oak_linux_boot_params::CC_BLOB_SEV_INFO_MAGIC {
                panic!("CCBlobSevInfo data structure has invalid magic: {}", magic);
            }
            let cpuid = unsafe { &*(cc_blob.cpuid_phys as *const CpuidPage) };
            let secrets = unsafe { &*(cc_blob.secrets_phys as *const SecretsPage) };

            log::info!("CPUID page: {:?}", cpuid);
            log::info!("Secrets page: {:?}", secrets);
        } else {
            log::warn!("CCSetupData data structure not found in setup_data");
        }
    }
    panic!();
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    let sev_status = get_sev_status().unwrap_or(SevStatus::empty());
    if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
        let mut ghcb_protocol = crate::ghcb::init_ghcb(sev_status.contains(SevStatus::SNP_ACTIVE));
        // Use the i8042 device to shut down the machine. Assumes the VMM exposes the device.
        // This is safe as both qemu and crosvm expose the i8042 device by default.
        let _ = ghcb_protocol.io_write_u8(0x64, 0xFE);
    } else {
        // Trigger a breakpoint exception. As we don't have a #BP handler, this will triple fault
        // and terminate the program.
        int3();
    }

    // But if we're still here for some reason, just go in an infinite halt loop.
    loop {
        hlt();
    }
}
