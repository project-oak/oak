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

use alloc::boxed::Box;
use core::mem::MaybeUninit;

pub use accept_memory::*;
pub use cpuid::*;
pub use dice_attestation::*;
pub use mmio::*;
pub use msr::*;
use oak_core::sync::OnceCell;
use oak_dice::evidence::TeePlatform;
use oak_linux_boot_params::BootE820Entry;
use oak_sev_guest::{ap_jump_table::ApJumpTable, ghcb::GhcbProtocol, msr::SevStatus};
pub use port::*;
use spinning_top::{lock_api::MutexGuard, RawSpinlock, Spinlock};
use x86_64::{PhysAddr, VirtAddr};

use crate::{paging::PageEncryption, sev::Shared, zero_page::ZeroPage, BootAllocator, BOOT_ALLOC};

#[link_section = ".boot"]
#[no_mangle]
static mut SEV_SECRETS: MaybeUninit<oak_sev_guest::secrets::SecretsPage> = MaybeUninit::uninit();
#[link_section = ".boot"]
#[no_mangle]
static SEV_CPUID: MaybeUninit<oak_sev_guest::cpuid::CpuidPage> = MaybeUninit::uninit();
#[no_mangle]
#[link_section = ".ap_bss"]
pub static AP_JUMP_TABLE: MaybeUninit<ApJumpTable> = MaybeUninit::uninit();

static GHCB_WRAPPER: Ghcb = Ghcb::new();

pub struct Ghcb {
    ghcb: OnceCell<Spinlock<GhcbProtocol<'static, oak_sev_guest::ghcb::Ghcb>>>,
}

impl Ghcb {
    const fn new() -> Self {
        Self { ghcb: OnceCell::new() }
    }

    pub fn init(&self, alloc: &'static BootAllocator) {
        let ghcb = Shared::leak(Shared::new_in(oak_sev_guest::ghcb::Ghcb::default(), alloc));
        ghcb.reset();

        // We can't use `.expect()` here as Spinlock doesn't implement `fmt::Debug`.
        if self
            .ghcb
            .set(Spinlock::new(GhcbProtocol::new(ghcb, |vaddr: VirtAddr| {
                Some(PhysAddr::new(vaddr.as_u64()))
            })))
            .is_err()
        {
            panic!("couldn't initialize GHCB wrapper");
        }

        // SNP requires that the GHCB is registered with the hypervisor.
        if sev_status().contains(SevStatus::SNP_ACTIVE) {
            self.get()
                .unwrap()
                .register_with_hypervisor()
                .expect("couldn't register the GHCB address with the hypervisor");
        }
    }

    /// Deallocates the GHCB block.
    ///
    /// # Safety
    ///
    /// The caller needs to guarantee that nobody has a reference to the GHCB
    /// when this function is called and that nobody will try to use the GHCB
    /// after the function returns.
    pub unsafe fn deinit(&self, alloc: &'static BootAllocator) {
        let ghcb = self.ghcb.deinit().unwrap().into_inner().into_inner();
        let _ = Shared::from_raw_in(ghcb, alloc);
    }

    pub fn get(
        &self,
    ) -> Option<MutexGuard<'_, RawSpinlock, GhcbProtocol<'static, oak_sev_guest::ghcb::Ghcb>>> {
        self.ghcb.get().map(|mutex| mutex.lock())
    }
}

/// Returns the value of the SEV_STATUS MSR that's safe to read even if the CPU
/// doesn't support it.
///
/// This function is intentionally not public; nobody outside the `hal::sev`
/// crate should care about this. If you need access to this from outside
/// `hal::sev`, that's a good indication some of the code should be in the HAL.
///
/// Initialized in the bootstrap assembly code.
fn sev_status() -> SevStatus {
    // Will be set in the bootstrap assembly code where we have to read the MSR
    // anyway.
    #[no_mangle]
    static mut SEV_STATUS: SevStatus = SevStatus::empty();

    // Safety: we don't allow mutation and this is initialized in the bootstrap
    // assembly.
    unsafe { SEV_STATUS }
}

pub fn early_initialize_platform() {
    // If we're under SEV-ES or SNP, we need a GHCB block for communication (SNP
    // implies SEV-ES).
    if sev_status().contains(SevStatus::SEV_ES_ENABLED) {
        GHCB_WRAPPER.init(&BOOT_ALLOC);
    }
    if sev_status().contains(SevStatus::SEV_ENABLED) {
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
    log::info!("Enabled SEV features: {:?}", sev_status());
    if sev_status().contains(SevStatus::SNP_ACTIVE) {
        dice_attestation::init_guest_message_encryptor()
            .expect("couldn't initialize guest message encryptor");
        accept_memory::validate_memory(e820_table)
    }

    // Register the AP Jump Table, if required.
    if sev_status().contains(SevStatus::SEV_ES_ENABLED) {
        // This assumes identity mapping. Which we have in stage0.
        let jump_table_pa = AP_JUMP_TABLE.as_ptr() as u64;
        if sev_status().contains(SevStatus::SNP_ACTIVE) {
            // Under SNP we need to place the jump table address in the secrets page.
            // Safety: we don't care about the contents of the secrets page beyond writing
            // our jump table address into it.
            let secrets = unsafe { SEV_SECRETS.assume_init_mut() };
            secrets.guest_area_0.ap_jump_table_pa = jump_table_pa;
        } else {
            // Plain old SEV-ES, use the GHCB protocol.
            if let Some(mut ghcb) = GHCB_WRAPPER.get() {
                ghcb.set_ap_jump_table(PhysAddr::new(jump_table_pa))
                    .expect("failed to set AP Jump Table");
            }
        }
    }
}

pub fn populate_zero_page(zero_page: &mut ZeroPage) {
    if sev_status().contains(SevStatus::SNP_ACTIVE) {
        // Safety: we're only interested in the pointer value of SEV_SECRETS, not its
        // contents.
        let cc_blob = Box::leak(Box::new_in(
            oak_linux_boot_params::CCBlobSevInfo::new(
                unsafe { SEV_SECRETS.as_ptr() },
                SEV_CPUID.as_ptr(),
            ),
            &BOOT_ALLOC,
        ));
        let setup_data =
            Box::leak(Box::new_in(oak_linux_boot_params::CCSetupData::new(cc_blob), &BOOT_ALLOC));

        zero_page.add_setup_data(setup_data);
    }
}

pub fn deinit_platform() {
    if sev_status().contains(SevStatus::SNP_ACTIVE) && GHCB_WRAPPER.get().is_some() {
        // Safety: we're in the last moments of stage0 and nobody should access the GHCB
        // beyond this point.
        unsafe { GHCB_WRAPPER.deinit(&BOOT_ALLOC) };
    }
}

pub fn tee_platform() -> TeePlatform {
    if sev_status().contains(SevStatus::SNP_ACTIVE) {
        TeePlatform::AmdSevSnp
    } else {
        TeePlatform::None
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
    if sev_status().contains(SevStatus::SEV_ENABLED) {
        match encryption_state {
            PageEncryption::Encrypted => encrypted(),
            PageEncryption::Unencrypted => 0,
        }
    } else {
        0
    }
}
