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

use crate::{
    acpi_tables::{LocalApicFlags, Madt, ProcessorLocalApic, ProcessorLocalX2Apic, Rsdp},
    apic::Lapic,
    pic::disable_pic8259,
};
use core::{
    arch::x86_64::_mm_pause,
    ffi::c_void,
    mem::MaybeUninit,
    sync::atomic::{AtomicU32, Ordering},
};
use oak_sev_guest::ap_jump_table::ApJumpTable;
use x86_64::PhysAddr;

extern "C" {
    #[link_name = "ap_start"]
    static AP_START: c_void;
}

// This symbol will be referenced from outside Rust, from the AP bootstrap code, to denote that an
// AP has become alive. It's in a special magic section as we have to ensure it's in the first 64K
// fo memory (or: the first segment).
#[no_mangle]
#[link_section = ".ap_bss"]
static LIVE_AP_COUNT: AtomicU32 = AtomicU32::new(0);

#[no_mangle]
#[link_section = ".ap_bss"]
pub static AP_JUMP_TABLE: MaybeUninit<ApJumpTable> = MaybeUninit::uninit();

pub fn start_ap(lapic: &mut Lapic, physical_apic_id: u32) -> Result<(), &'static str> {
    lapic.send_init_ipi(physical_apic_id)?;
    // TODO(#4235): wait 10 ms. The numbers chosen here are arbitrary and have no connection to
    // actual seconds.
    for _ in 1..(1 << 15) {
        // Safety: SSE2 is supported in all 64-bit processors.
        unsafe { _mm_pause() };
    }
    // We assume that we're not going to call start_ap() concurrently, so there is no race condition
    // here. Which should be true, as we don't have threads and this is running on the sole BSP.
    let current_live_count = LIVE_AP_COUNT.load(Ordering::SeqCst);
    // Safety: we're not going to dereference the memory, we're just interested in the pointer
    // value.
    let vector = unsafe { &AP_START as *const _ as u64 };
    lapic.send_startup_ipi(physical_apic_id, PhysAddr::new(vector))?;
    // TODO(#4235): wait 200 us (instead of _some_ unknown amount of time); send SIPI again if the
    // core hasn't started
    for _ in 1..(1 << 20) {
        // Safety: SSE2 is supported in all 64-bit processors.
        unsafe { _mm_pause() };
        if LIVE_AP_COUNT.load(Ordering::SeqCst) > current_live_count {
            // it's alive!
            break;
        }
    }
    if LIVE_AP_COUNT.load(Ordering::SeqCst) == current_live_count {
        // TODO(#4235): try sending a second SIPI before giving up on the AP
        log::warn!("AP {} failed to start up", physical_apic_id);
    }
    Ok(())
}

// TODO(#4235): Bootstrap the APs.
pub fn bootstrap_aps(rsdp: &Rsdp) -> Result<(), &'static str> {
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
    unsafe { disable_pic8259()? };
    let mut lapic = Lapic::enable()?;

    let local_apic_id = lapic.local_apic_id();

    // How many APs do we expect to come online?
    let mut expected_aps = 0;

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

        expected_aps += 1;
        start_ap(&mut lapic, remote_lapic_id)?;
    }

    // Wait until all APs have told they are online. Or we time out waiting for them.
    // The timeout has been chosen arbitrarily and may need to be tuned.
    for _ in 0..(1 << 23) {
        if LIVE_AP_COUNT.load(Ordering::SeqCst) == expected_aps {
            break;
        }
        // Safety: SSE2 is supported in all 64-bit processors.
        unsafe { _mm_pause() };
    }
    log::info!(
        "Expected number of APs: {}, started number of APs: {}",
        expected_aps,
        LIVE_AP_COUNT.load(Ordering::SeqCst)
    );

    if LIVE_AP_COUNT.load(Ordering::SeqCst) != expected_aps {
        return Err("not all APs came online");
    }

    Ok(())
}
