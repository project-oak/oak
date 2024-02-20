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
#![feature(naked_functions)]

use core::{arch::asm, panic::PanicInfo};

use lazy_static::lazy_static;
use oak_linux_boot_params::{BootParams, CCBlobSevInfo, CCSetupData, SetupDataType};
use oak_sev_snp_guest::{
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

/// Crude implementation of a #GP handler that emulates any `rdmsr` instructions that trigger #GP.
///
/// This function emulates the `rdmsr` instruction by returning 0 in RAX and RDX.
#[naked]
extern "x86-interrupt" fn gp_handler(_: InterruptStackFrame, _: u64) {
    unsafe {
        asm! {
            "mov 8(%rsp), %rax",    // rax = rsp + 16 (address of the return RIP)
            "cmpw $0x320F, (%rax)", // is RIP pointing to 0x320F (RDMSR)?
            "jne 2f",               // if not, jump to label 2
            "add $2, %rax",         // increment rax by 2 (size of RDMSR instruction)
            "add $16, %rsp",        // drop the error code and old RIP from stack
            "push %rax",            // put Return RIP back onto the stack for iretq
            "xor %rax, %rax",       // zero out RAX
            "xor %rdx, %rdx",       // zero out RDX
            "iretq",                // and go back claiming we've executed the RDMSR
            "2:",                   // it wasn't RDMSR
            "int $8",               // cause a double fault
            options(att_syntax, noreturn)
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
        let mut setup_data = boot_params.hdr.setup_data();

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
