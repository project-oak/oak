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
use oak_sev_guest::io::{IoPortFactory, PortReader, PortWriter};
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

/// Whether a memory page is private to the guest or shared with the hypervisor.
#[derive(Copy, Clone, Debug)]
pub enum PageAssignment {
    Shared,
    Private,
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
    fn early_initialize_platform();

    /// Platform-specific intialization.
    ///
    /// This gets executed after `early_initalize_platform()` and some other
    /// auxiliary services, such as logging, have been set up; the main purpose
    /// is to accept all guest memory so that we can set up a heap
    /// allocator.
    ///
    /// This does mean you do not have access to the heap allocator
    /// (BOOT_ALLOCATOR will still work).
    fn initialize_platform(e820_table: &[BootE820Entry]);

    /// Platform-specific cleanups just before stage0 jumps to the kernel.
    ///
    /// The assumption is that after this operation there will no longer be any
    /// memory allocations or uses of the logging interface.
    fn deinit_platform();

    /// Populates platform-specific information in the zero page.
    ///
    /// Example: locations of the SEV Secrets and CPUID pages.
    fn populate_zero_page(zero_page: &mut ZeroPage);

    /// Returns an attestation report.
    ///
    /// If AMD SEV-SNP is enabled it returns a valid hardware-rooted attestation
    /// report. In other cases it generates an empty attestation report for
    /// testing. The additional data will be set in both cases to bind the
    /// DICE chain to the attestation report.
    ///
    /// # Arguments
    ///
    /// * `report_data` - The custom data that must be included in the report.
    ///   This is typically used to bind information (such as the hash of a
    ///   public key) to the report.
    fn get_attestation(
        report_data: [u8; REPORT_DATA_SIZE],
    ) -> Result<AttestationReport, &'static str>;

    /// Requests a derived key.
    ///
    /// The key is derived from the VCEK. The key derivation mixes in the VM
    /// launch measurement and guest policy and uses VMPL0.
    ///
    /// We use this key as the unique device secret for deriving compound
    /// devices identifiers for each layer, and eventually a sealing key in
    /// the last layer.
    fn get_derived_key() -> Result<DerivedKey, &'static str>;

    /// Ask for the page state to be changed by the hypervisor.
    fn change_page_state(page: Page<Size4KiB>, state: PageAssignment);

    /// Validate one page of memory.
    ///
    /// This operation is required for SEV after going from a SHARED state to a
    /// PRIVATE state.
    fn revalidate_page(page: Page<Size4KiB>);

    /// Mask to use in the page tables for the given encrypion state.
    ///
    /// SEV and TDX have opposite behaviours: for SEV, encrypted pages are
    /// marked; for TDX, unencrypted pages are marked.
    fn page_table_mask(encryption_state: PageEncryption) -> u64;

    /// Encrypted/shared bit mask irrespective of its semantics.
    fn encrypted() -> u64;

    fn tee_platform() -> TeePlatform;

    /// Read a MSR.
    ///
    /// ## Safety
    ///
    /// The caller must guarantee that the MSR is valid.
    unsafe fn read_msr(msr: u32) -> u64;

    /// Write to a MSR.
    ///
    /// ## Safety
    ///
    /// The caller must guarantee that the MSR is valid.
    unsafe fn write_msr(msr: u32, value: u64);
}
pub use base::Base;
#[cfg(feature = "sev")]
pub use sev::Sev;

/// Wrapper that can access a MSR either directly or through the GHCB, depending
/// on the environment.
pub struct Msr {
    msr_id: u32,
}

impl Msr {
    pub const fn new(reg: u32) -> Self {
        Self { msr_id: reg }
    }

    /// Read the MSR.
    ///
    /// ## Safety
    ///
    /// The caller must guarantee that the MSR is valid.
    pub unsafe fn read<P: Platform>(&self) -> u64 {
        P::read_msr(self.msr_id)
    }

    /// Write the MSR.
    ///
    /// ## Safety
    ///
    /// The caller must guarantee that the MSR is valid.
    pub unsafe fn write<P: Platform>(&mut self, val: u64) {
        P::write_msr(self.msr_id, val);
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
