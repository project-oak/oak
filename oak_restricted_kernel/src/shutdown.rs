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

use core::arch::asm;

use oak_sev_guest::{
    io::{IoPortFactory, PortFactoryWrapper, PortWrapper, PortWriter},
    msr::{SevStatus, TerminationReason, TerminationRequest, get_sev_status, request_termination},
};
use x86_64::{VirtAddr, instructions::tables::lidt, structures::DescriptorTablePointer};

/// Tries various ways to shut down the machine.
pub fn shutdown() -> ! {
    // 1. Attempt the SEV-ES shutdown protocol, if we're under SEV-ES.
    let sev_status = get_sev_status().unwrap_or(SevStatus::empty());
    if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
        request_termination(TerminationRequest { reason: TerminationReason::General });
    }

    // 2. If we're still here, attempt shutdown via i8042.
    let port_factory = if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
        crate::ghcb::get_ghcb_port_factory()
    } else {
        PortFactoryWrapper::new_raw()
    };
    let mut port: PortWrapper<u8> = port_factory.new_writer(0x64);
    // This is safe as both qemu and crosvm expose the i8042 device by default.
    unsafe {
        let _ = port.try_write(0xFE_u8);
    }

    // 3. If we're still here, the gloves come off. Load a garbage IDT and cause
    //    #UD.
    let idt = DescriptorTablePointer { limit: 0, base: VirtAddr::new(0x0) };
    // Safety: this is technically safe, as it will cause the machine to crash, and
    // that's the intent.
    unsafe {
        lidt(&idt);
        asm! {
            "ud2",
            options(noreturn)
        }
    }
}
