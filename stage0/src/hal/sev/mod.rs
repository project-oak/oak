//
// Copyright 2024 The Project Oak Authors
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

mod accept_memory;
mod cpuid;
mod dice_attestation;
mod mmio;
mod msr;
mod port;

pub use accept_memory::*;
pub use cpuid::*;
pub use dice_attestation::*;
pub use mmio::*;
pub use msr::*;
use oak_linux_boot_params::BootE820Entry;
use oak_sev_guest::msr::SevStatus;
pub use port::*;

use crate::{paging::PageEncryption, BOOT_ALLOC};

pub fn early_initialize_platform() {
    // If we're under SEV-ES or SNP, we need a GHCB block for communication (SNP
    // implies SEV-ES).
    if crate::sev_status().contains(SevStatus::SEV_ES_ENABLED) {
        crate::sev::GHCB_WRAPPER.init(&BOOT_ALLOC);
    }
    if crate::sev_status().contains(SevStatus::SEV_ENABLED) {
        // Safety: This is safe for SEV-ES and SNP because we're using an originally
        // supported mode of the Pentium 6: Write-protect, with MTRR enabled.
        // If we get CPUID reads working, we may want to check that MTRR is
        // supported, but only if we want to support very old processors.
        // However, note that, this branch is only executed if
        // we have encryption, and this wouldn't be true for very old processors.
        unsafe {
            crate::msr::MTRRDefType::write(
                crate::msr::MTRRDefTypeFlags::MTRR_ENABLE,
                crate::msr::MemoryType::WP,
            );
        }
    }
}

pub fn initialize_platform(e820_table: &[BootE820Entry]) {
    log::info!("Enabled SEV features: {:?}", crate::sev_status());
    if crate::sev_status().contains(SevStatus::SNP_ACTIVE) {
        dice_attestation::init_guest_message_encryptor()
            .expect("couldn't initialize guest message encryptor");
        accept_memory::validate_memory(e820_table)
    }
}

/// Returns the location of the ENCRYPTED bit when running under AMD SEV.
pub(crate) fn encrypted() -> u64 {
    #[no_mangle]
    static mut ENCRYPTED: u64 = 0;

    // Safety: we don't allow mutation and this is initialized in the bootstrap
    // assembly.
    unsafe { ENCRYPTED }
}

pub fn page_table_mask(encryption_state: PageEncryption) -> u64 {
    if crate::sev_status().contains(SevStatus::SEV_ENABLED) {
        match encryption_state {
            PageEncryption::Encrypted => encrypted(),
            PageEncryption::Unencrypted => 0,
        }
    } else {
        0
    }
}
