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

mod base;
#[cfg(feature = "sev")]
mod sev;

use core::arch::x86_64::CpuidResult;

use oak_dice::evidence::TeePlatform;
use oak_linux_boot_params::BootE820Entry;
use oak_sev_guest::{
    io::{IoPortFactory, PortReader, PortWriter},
    msr::PageAssignment,
};
use oak_sev_snp_attestation_report::{AttestationReport, REPORT_DATA_SIZE};
use oak_stage0_dice::DerivedKey;
use x86_64::{
    structures::{
        paging::{Page, PageSize, Size4KiB},
        port::{PortRead, PortWrite},
    },
    PhysAddr,
};

use crate::{paging::PageEncryption, zero_page::ZeroPage};

/// Abstraction around MMIO (memory-mapped I/O) read/write access.
///
/// Normally you can just access the memory directly via
/// `read_volatile`/`write_volatile`, but for SEV-ES and above we need to go via
/// the GHCB to do MMIO.
pub trait Mmio<S: PageSize> {
    /// Reads an u32 from the MMIO memory region.
    ///
    /// The offset is the number of u32-s (not byte offsets); that is, to read
    /// bytes at [base_address+4, base_address+8) the offset needs to be 1.
    ///
    /// Panics if the read would go outside the memory range.
    fn read_u32(&self, offset: usize) -> u32;

    /// Write an u32 from the MMIO memory region.
    ///
    /// The offset is the number of u32-s (not byte offsets); that is, to read
    /// bytes at [base_address+4, base_address+8) the offset needs to be 1.
    ///
    /// Panics if the read would go outside the memory range.
    ///
    /// The caller needs to guarantee that the value is valid for the register
    /// it is written to.
    unsafe fn write_u32(&mut self, offset: usize, value: u32);
}

pub trait Platform {
    type Mmio<S: PageSize>: Mmio<S>;

    /// Performs the CPUID instruction.
    fn cpuid(leaf: u32) -> CpuidResult;

    unsafe fn mmio<S: PageSize>(base_address: PhysAddr) -> Self::Mmio<S>;

    unsafe fn read_u8_from_port(port: u16) -> Result<u8, &'static str>;
    unsafe fn write_u8_to_port(port: u16, value: u8) -> Result<(), &'static str>;
    unsafe fn read_u16_from_port(port: u16) -> Result<u16, &'static str>;
    unsafe fn write_u16_to_port(port: u16, value: u16) -> Result<(), &'static str>;
    unsafe fn read_u32_from_port(port: u16) -> Result<u32, &'static str>;
    unsafe fn write_u32_to_port(port: u16, value: u32) -> Result<(), &'static str>;
}
pub use base::Base;
#[cfg(feature = "sev")]
pub use sev::Sev;

/// Wrapper that can access a MSR either directly or through the GHCB, depending
/// on the environment.
pub struct Msr {
    #[cfg(feature = "sev")]
    msr_id: u32,
    msr: base::Msr,
}

impl Msr {
    pub const fn new(reg: u32) -> Self {
        Self {
            #[cfg(feature = "sev")]
            msr_id: reg,
            msr: base::Msr::new(reg),
        }
    }

    /// Read the MSR.
    ///
    /// ## Safety
    ///
    /// The caller must guarantee that the MSR is valid.
    pub unsafe fn read(&self) -> u64 {
        #[cfg(feature = "sev")]
        return sev::read_msr(&self.msr, self.msr_id);
        #[cfg(not(feature = "sev"))]
        return self.msr.read();
    }

    /// Write the MSR.
    ///
    /// ## Safety
    ///
    /// The caller must guarantee that the MSR is valid.
    pub unsafe fn write(&mut self, val: u64) {
        #[cfg(feature = "sev")]
        return sev::write_msr(&mut self.msr, self.msr_id, val);
        #[cfg(not(feature = "sev"))]
        return self.msr.write(val);
    }
}

#[derive(Clone)]
pub struct PortFactory {
    read_u8: unsafe fn(u16) -> Result<u8, &'static str>,
    read_u16: unsafe fn(u16) -> Result<u16, &'static str>,
    read_u32: unsafe fn(u16) -> Result<u32, &'static str>,
    write_u8: unsafe fn(u16, u8) -> Result<(), &'static str>,
    write_u16: unsafe fn(u16, u16) -> Result<(), &'static str>,
    write_u32: unsafe fn(u16, u32) -> Result<(), &'static str>,
}

impl PortFactory {
    pub fn new<P: Platform>() -> Self {
        Self {
            read_u8: P::read_u8_from_port,
            read_u16: P::read_u16_from_port,
            read_u32: P::read_u32_from_port,
            write_u8: P::write_u8_to_port,
            write_u16: P::write_u16_to_port,
            write_u32: P::write_u32_to_port,
        }
    }
}

impl IoPortFactory<'_, u8, Port<u8>, Port<u8>> for PortFactory {
    fn new_reader(&self, port: u16) -> Port<u8> {
        Port::new(port, self.read_u8, self.write_u8)
    }

    fn new_writer(&self, port: u16) -> Port<u8> {
        Port::new(port, self.read_u8, self.write_u8)
    }
}

impl IoPortFactory<'_, u16, Port<u16>, Port<u16>> for PortFactory {
    fn new_reader(&self, port: u16) -> Port<u16> {
        Port::new(port, self.read_u16, self.write_u16)
    }

    fn new_writer(&self, port: u16) -> Port<u16> {
        Port::new(port, self.read_u16, self.write_u16)
    }
}

impl IoPortFactory<'_, u32, Port<u32>, Port<u32>> for PortFactory {
    fn new_reader(&self, port: u16) -> Port<u32> {
        Port::new(port, self.read_u32, self.write_u32)
    }

    fn new_writer(&self, port: u16) -> Port<u32> {
        Port::new(port, self.read_u32, self.write_u32)
    }
}

pub struct Port<T: PortRead + PortWrite> {
    port: u16,
    read: unsafe fn(u16) -> Result<T, &'static str>,
    write: unsafe fn(u16, T) -> Result<(), &'static str>,
}

impl<T: PortRead + PortWrite> Port<T> {
    fn new(
        port: u16,
        read: unsafe fn(u16) -> Result<T, &'static str>,
        write: unsafe fn(u16, T) -> Result<(), &'static str>,
    ) -> Self {
        Self { port, read, write }
    }
}

impl<T: PortRead + PortWrite> PortReader<T> for Port<T> {
    unsafe fn try_read(&mut self) -> Result<T, &'static str> {
        (self.read)(self.port)
    }
}

impl<T: PortRead + PortWrite> PortWriter<T> for Port<T> {
    unsafe fn try_write(&mut self, value: T) -> Result<(), &'static str> {
        (self.write)(self.port, value)
    }
}

/// Platform-specific early initialization.
///
/// This sets up the bare minimum to get things going; for example, under
/// SEV-ES and above, we set up the GHCB here, but nothing more.
///
/// This gets executed very soon after stage0 starts and comes with many
/// restrictions:
///   - You do not have access to logging.
///   - You do not have access to heap allocator (BOOT_ALLOCATOR will still
///     work).
pub fn early_initialize_platform() {
    #[cfg(feature = "sev")]
    sev::early_initialize_platform();
}

/// Platform-specific intialization.
///
/// This gets executed after `early_initalize_platform()` and some other
/// auxiliary services, such as logging, have been set up; the main purpose is
/// to accept all guest memory so that we can set up a heap allocator.
///
/// This does mean you do not have access to the heap allocator (BOOT_ALLOCATOR
/// will still work).
pub fn initialize_platform(e820_table: &[BootE820Entry]) {
    #[cfg(feature = "sev")]
    sev::initialize_platform(e820_table)
}

/// Platform-specific cleanups just before stage0 jumps to the kernel.
///
/// The assumption is that after this operation there will no longer be any
/// memory allocations or uses of the logging interface.
pub fn deinit_platform() {
    #[cfg(feature = "sev")]
    sev::deinit_platform();
}

pub fn populate_zero_page(zero_page: &mut ZeroPage) {
    #[cfg(feature = "sev")]
    sev::populate_zero_page(zero_page);
}

/// Returns an attestation report.
///
/// If AMD SEV-SNP is enabled it returns a valid hardware-rooted attestation
/// report. In other cases it generates an empty attestation report for testing.
/// The additional data will be set in both cases to bind the DICE chain to the
/// attestation report.
///
/// # Arguments
///
/// * `report_data` - The custom data that must be included in the report. This
///   is typically used to bind information (such as the hash of a public key)
///   to the report.
pub fn get_attestation(
    report_data: [u8; REPORT_DATA_SIZE],
) -> Result<AttestationReport, &'static str> {
    #[cfg(feature = "sev")]
    return sev::get_attestation(report_data);
    #[cfg(not(feature = "sev"))]
    return base::get_attestation(report_data);
}

/// Requests a derived key.
///
/// The key is derived from the VCEK. The key derivation mixes in the VM launch
/// measurement and guest policy and uses VMPL0.
///
/// We use this key as the unique device secret for deriving compound devices
/// identifiers for each layer, and eventually a sealing key in the last layer.
pub fn get_derived_key() -> Result<DerivedKey, &'static str> {
    #[cfg(feature = "sev")]
    return sev::get_derived_key();
    #[cfg(not(feature = "sev"))]
    return base::get_derived_key();
}

/// Ask for the page state to be changed by the hypervisor.
pub fn change_page_state(page: Page<Size4KiB>, state: PageAssignment) {
    #[cfg(feature = "sev")]
    sev::change_page_state(page, state).unwrap();
}

/// Validate one page of memory.
///
/// This operation is required for SEV after going from a SHARED state to a
/// PRIVATE state.
pub fn revalidate_page(page: Page<Size4KiB>) {
    #[cfg(feature = "sev")]
    sev::revalidate_page(page).unwrap();
}

/// Mask to use in the page tables for the given encrypion state.
///
/// SEV and TDX have opposite behaviours: for SEV, encrypted pages are marked;
/// for TDX, unencrypted pages are marked.
pub fn page_table_mask(encryption_state: PageEncryption) -> u64 {
    #[cfg(feature = "sev")]
    return sev::page_table_mask(encryption_state);
    #[cfg(not(feature = "sev"))]
    return 0;
}

/// Encrypted/shared bit mask irrespective of its semantics.
pub fn encrypted() -> u64 {
    #[cfg(feature = "sev")]
    return sev::encrypted();
    #[cfg(not(feature = "sev"))]
    return 0;
}

pub fn tee_platform() -> TeePlatform {
    #[cfg(feature = "sev")]
    return sev::tee_platform();
    #[cfg(not(feature = "sev"))]
    return TeePlatform::None;
}
