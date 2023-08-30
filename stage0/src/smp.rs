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

use core::{arch::x86_64::_mm_pause, ffi::c_void};

use oak_sev_guest::io::PortFactoryWrapper;
use x86_64::PhysAddr;

use crate::{
    acpi_tables::{LocalApicFlags, Madt, ProcessorLocalApic, ProcessorLocalX2Apic, Rsdp},
    apic::Lapic,
    pic::disable_pic8259,
};

extern "C" {
    #[link_name = "ap_start"]
    static AP_START: c_void;
}

pub fn start_ap(lapic: &mut Lapic, physical_apic_id: u32) -> Result<(), &'static str> {
    lapic.send_init_ipi(physical_apic_id)?;
    // TODO(#4235): wait 10 ms. The numbers chosen here are arbitrary and have no connection to
    // actual seconds.
    for _ in 1..(1 << 15) {
        // Safety: SSE2 is supported in all 64-bit processors.
        unsafe { _mm_pause() };
    }
    // Safety: we're not going to dereference the memory, we're just interested in the pointer
    // value.
    // We also mask the high bits, as the AP will be in the 'magic' real mode that reads data from
    // the end of the 4 GiB space (aka the BIOS area) much like the BSP.
    let vector = unsafe { &AP_START as *const _ as u64 } & 0xFFFFF;
    lapic.send_startup_ipi(physical_apic_id, PhysAddr::new(vector))?;
    // TODO(#4235): wait 200 us (instead of _some_ unknown amount of time); send SIPI again if the
    // core hasn't started
    for _ in 1..(1 << 12) {
        // Safety: SSE2 is supported in all 64-bit processors.
        unsafe { _mm_pause() };
    }
    Ok(())
}

// TODO(#4235): Bootstrap the APs.
pub fn bootstrap_aps(rsdp: &Rsdp, port_factory: &PortFactoryWrapper) -> Result<(), &'static str> {
    // If XSDT exists, then per ACPI spec we have to prefer that. If it doesn't, see if we can use
    // the old RSDT. (If we have neither XSDT or RSDT, the ACPI tables are broken.)
    let madt = if let Ok(Some(xsdt)) = rsdp.xsdt() {
        xsdt.get(Madt::SIGNATURE)
            .ok_or("MADT table not found in XSDT")?
    } else {
        let rsdt = rsdp.rsdt()?.ok_or("RSDT not found")?;
        rsdt.get(Madt::SIGNATURE)
            .ok_or("MADT table not found in RSDT")?
    };
    let madt = Madt::new(madt).expect("invalid MADT");

    // Disable the local PIC and set up our local APIC, as we need to send IPIs to APs via the APIC.
    // Safety: we can reasonably expect the PICs to be available.
    unsafe { disable_pic8259(port_factory)? };
    let mut lapic = Lapic::enable()?;

    let local_apic_id = lapic.local_apic_id();

    // APIC and X2APIC structures are largely the same; X2APIC entries are used if the APIC ID is
    // too large to fit into the one-byte field of the APIC structure (e.g. if you have more than
    // 256 CPUs).
    for item in madt.iter() {
        let (remote_lapic_id, flags) = match item.structure_type {
            ProcessorLocalApic::STRUCTURE_TYPE => {
                let remote_lapic = ProcessorLocalApic::new(item)?;
                log::debug!("Local APIC: {:?}", remote_lapic);
                (remote_lapic.apic_id as u32, remote_lapic.flags)
            }
            ProcessorLocalX2Apic::STRUCTURE_TYPE => {
                let remote_lapic = ProcessorLocalX2Apic::new(item)?;
                log::debug!("Local X2APIC: {:?}", remote_lapic);
                (remote_lapic.x2apic_id, remote_lapic.flags)
            }
            // We don't care about other interrupt controller structure types.
            _ => {
                log::debug!("uninteresting structure: {}", item.structure_type);
                continue;
            }
        };

        if remote_lapic_id == local_apic_id {
            // Don't wake ourselves.
            continue;
        }
        if !flags.contains(LocalApicFlags::ENABLED) {
            // Don't wake disabled CPUs.
            continue;
        }

        start_ap(&mut lapic, remote_lapic_id)?;
    }

    Ok(())
}
