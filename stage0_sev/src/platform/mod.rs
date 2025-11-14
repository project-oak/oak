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
mod dice_attestation;
mod mmio;
mod smp;

#[cfg(feature = "sev_kernel_hashes")]
mod kernel_hash_tables;

use alloc::boxed::Box;
use core::{arch::x86_64::CpuidResult, mem::MaybeUninit};

use oak_attestation::dice::DiceAttester;
use oak_core::sync::OnceCell;
use oak_dice::evidence::TeePlatform;
use oak_linux_boot_params::BootE820Entry;
use oak_sev_guest::{
    ap_jump_table::ApJumpTable, cpuid::CpuidInput, ghcb::GhcbProtocol, msr::SevStatus,
};
use oak_stage0::{
    allocator::Shared,
    hal::{Base, PageAssignment, Platform, PortFactory},
    paging::PageEncryption,
    BootAllocator, Rsdp, ZeroPage, BOOT_ALLOC,
};
use spinning_top::{lock_api::MutexGuard, RawSpinlock, Spinlock};
use x86_64::{structures::paging::PageSize, PhysAddr, VirtAddr};
use zerocopy::{FromBytes, IntoBytes};

#[link_section = ".boot"]
#[no_mangle]
static mut SEV_SECRETS: MaybeUninit<oak_sev_guest::secrets::SecretsPage> = MaybeUninit::uninit();
#[link_section = ".boot"]
#[no_mangle]
static SEV_CPUID: MaybeUninit<oak_sev_guest::cpuid::CpuidPage> = MaybeUninit::uninit();
#[no_mangle]
#[link_section = ".ap_bss"]
pub static AP_JUMP_TABLE: MaybeUninit<ApJumpTable> = MaybeUninit::uninit();
#[cfg(feature = "sev_kernel_hashes")]
#[link_section = ".snp_hash_table"]
#[no_mangle]
static mut SEV_HASH_TABLE: MaybeUninit<kernel_hash_tables::PaddedSevHashTable> = MaybeUninit::uninit();

static GHCB_WRAPPER: Ghcb = Ghcb::new();

pub struct Ghcb {
    ghcb: OnceCell<Spinlock<GhcbProtocol<'static, oak_sev_guest::ghcb::Ghcb>>>,
}

impl Ghcb {
    const fn new() -> Self {
        Self { ghcb: OnceCell::new() }
    }

    pub fn init(&self, alloc: &'static BootAllocator) {
        let ghcb =
            Shared::leak(Shared::<_, _, Sev>::new_in(oak_sev_guest::ghcb::Ghcb::default(), alloc));
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
        let _ = Shared::<_, _, Sev>::from_raw_in(ghcb, alloc);
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

/// Returns the location of the ENCRYPTED bit when running under AMD SEV.
pub(crate) fn encrypted() -> u64 {
    #[no_mangle]
    static mut ENCRYPTED: u64 = 0;

    // Safety: we don't allow mutation and this is initialized in the bootstrap
    // assembly.
    unsafe { ENCRYPTED }
}

trait IntoMsrPageAssignment {
    fn into_msr(self) -> oak_sev_guest::msr::PageAssignment;
}

impl IntoMsrPageAssignment for PageAssignment {
    fn into_msr(self) -> oak_sev_guest::msr::PageAssignment {
        match self {
            PageAssignment::Shared => oak_sev_guest::msr::PageAssignment::Shared,
            PageAssignment::Private => oak_sev_guest::msr::PageAssignment::Private,
        }
    }
}

pub struct Sev {}

impl Platform for Sev {
    type Mmio<S: PageSize> = mmio::Mmio<S>;
    type Attester = DiceAttester;

    fn cpuid(leaf: u32) -> CpuidResult {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            ghcb.get_cpuid(CpuidInput { eax: leaf, ecx: 0, xcr0: 0, xss: 0 }).unwrap().into()
        } else {
            oak_stage0::hal::Base::cpuid(leaf)
        }
    }

    unsafe fn mmio<S: x86_64::structures::paging::PageSize>(
        base_address: PhysAddr,
    ) -> Self::Mmio<S> {
        mmio::Mmio::new(base_address)
    }

    fn port_factory() -> PortFactory {
        if GHCB_WRAPPER.get().is_some() {
            PortFactory {
                read_u8: |port| GHCB_WRAPPER.get().unwrap().io_read_u8(port),
                read_u16: |port| GHCB_WRAPPER.get().unwrap().io_read_u16(port),
                read_u32: |port| GHCB_WRAPPER.get().unwrap().io_read_u32(port),
                write_u8: |port, value| GHCB_WRAPPER.get().unwrap().io_write_u8(port, value),
                write_u16: |port, value| GHCB_WRAPPER.get().unwrap().io_write_u16(port, value),
                write_u32: |port, value| GHCB_WRAPPER.get().unwrap().io_write_u32(port, value),
            }
        } else {
            oak_stage0::hal::Base::port_factory()
        }
    }

    fn prefill_e820_table<T: IntoBytes + FromBytes>(_: &mut T) -> Result<usize, &'static str> {
        Err("SEV does not support E820 prefill")
    }

    fn early_initialize_platform() {
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
                oak_stage0::msr::MTRRDefType::write::<Sev>(
                    oak_stage0::msr::MTRRDefTypeFlags::MTRR_ENABLE,
                    oak_stage0::msr::MemoryType::WP,
                );
            }
        }
    }

    fn initialize_platform(e820_table: &[BootE820Entry]) {
        log::info!("Enabled SEV features: {:?}", sev_status());

        if sev_status().contains(SevStatus::SEV_ES_ENABLED) {
            let sev_info = oak_sev_guest::msr::get_sev_info().expect("couldn't get SEV info");
            if sev_info.min_protocol_version > 2 || sev_info.max_protocol_version < 2 {
                log::warn!(
                    "stage0 currently only supports GHCB protocol version 2, some features (like \
                    AP bootstrap) may not work. Platform reports min version {}, max version {}",
                    sev_info.min_protocol_version,
                    sev_info.max_protocol_version
                );
            }
        }
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

    fn finalize_acpi_tables(rsdp: &mut Rsdp) -> Result<(), &'static str> {
        // No further changes needed to ACPI tables, but now that they're in
        // place, we can bring up other CPUs (APs).
        let result = smp::bootstrap_aps::<Sev>(rsdp);
        if let Err(err) = result {
            log::warn!("Failed to bootstrap APs: {}. APs may not be properly initialized.", err);
        }
        result
    }

    fn populate_zero_page(zero_page: &mut ZeroPage) {
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
            let setup_data = Box::leak(Box::new_in(
                oak_linux_boot_params::CCSetupData::new(cc_blob),
                &BOOT_ALLOC,
            ));

            zero_page.add_setup_data(setup_data);
        }
    }

    fn deinit_platform() {
        if sev_status().contains(SevStatus::SNP_ACTIVE) && GHCB_WRAPPER.get().is_some() {
            // Safety: we're in the last moments of stage0 and nobody should access the GHCB
            // beyond this point.
            unsafe { GHCB_WRAPPER.deinit(&BOOT_ALLOC) };
        }
    }

    fn tee_platform() -> TeePlatform {
        if sev_status().contains(SevStatus::SNP_ACTIVE) {
            TeePlatform::AmdSevSnp
        } else {
            TeePlatform::None
        }
    }

    fn page_table_mask(encryption_state: PageEncryption) -> u64 {
        if sev_status().contains(SevStatus::SEV_ENABLED) {
            match encryption_state {
                PageEncryption::Unset => 0,
                PageEncryption::Encrypted => encrypted(),
                PageEncryption::Unencrypted => 0,
            }
        } else {
            0
        }
    }

    fn get_attester() -> Result<Self::Attester, &'static str> {
        dice_attestation::get_attester()
    }

    fn get_derived_key() -> Result<oak_stage0_dice::DerivedKey, &'static str> {
        dice_attestation::get_derived_key()
    }

    fn change_page_state(
        page: x86_64::structures::paging::Page<x86_64::structures::paging::Size4KiB>,
        state: PageAssignment,
    ) {
        accept_memory::change_page_state(page, state.into_msr())
            .expect("failed to change page state");
    }

    fn revalidate_page(
        page: x86_64::structures::paging::Page<x86_64::structures::paging::Size4KiB>,
    ) {
        accept_memory::revalidate_page(page).expect("failed to revalidate memory");
    }

    fn encrypted() -> u64 {
        encrypted()
    }

    unsafe fn read_msr(msr_id: u32) -> u64 {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            ghcb.msr_read(msr_id).expect("couldn't read the MSR using the GHCB protocol")
        } else {
            Base::read_msr(msr_id)
        }
    }

    unsafe fn write_msr(msr_id: u32, val: u64) {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            ghcb.msr_write(msr_id, val).expect("couldn't write the MSR using the GHCB protocol")
        } else {
            Base::write_msr(msr_id, val)
        }
    }

    fn wbvind() {
        Base::wbvind()
    }

    #[cfg(feature = "sev_kernel_hashes")]
    fn validate_measured_boot(
       cmdline: &[u8], initrd_digest: &[u8], kernel_setup_data: &[u8], kernel_bytes: &[u8]
    ) -> bool {
        log::debug!("validating measured boot primitives");
        // This address is well-defined by UEFI:
        // https://github.com/tianocore/edk2/blob/f98662c5e35b6ab60f46ee4350fa0e6eab0497cf/OvmfPkg/ResetVector/X64/OvmfSevMetadata.asm#L88-L91
        let sev_hash_table = 0x10c00 as *mut kernel_hash_tables::PaddedSevHashTable;
        let sev_hash_table = unsafe { &mut *sev_hash_table };
        let res = kernel_hash_tables::validate_hash_table(&sev_hash_table, cmdline, initrd_digest, kernel_setup_data, kernel_bytes);
        log::debug!("validated measured boot primitives");
        res
    }

    #[cfg(not(feature = "sev_kernel_hashes"))]
    fn validate_measured_boot(
       _cmdline: &[u8], _initrd_digest: &[u8], _kernel_setup_data: &[u8], _kernel_bytes: &[u8]
    ) -> bool {
        log::debug!("sev_kernel_hashes is not compiled, skipping");
        true
    }
}
