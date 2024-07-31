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

use core::{arch::x86_64::CpuidResult, marker::PhantomData, mem::size_of};

use oak_linux_boot_params::BootE820Entry;
use oak_sev_guest::io::{IoPortFactory, PortReader, PortWriter};
use x86_64::{
    structures::paging::{PageSize, Size4KiB},
    PhysAddr,
};

/// Abstraction around MMIO (memory-mapped I/O) read/write access.
///
/// Normally you can just access the memory directly via
/// `read_volatile`/`write_volatile`, but for SEV-ES and above we need to go via
/// the GHCB to do MMIO.
pub struct Mmio<S: PageSize = Size4KiB> {
    mmio: base::Mmio<S>,
}

impl<S: PageSize> Mmio<S> {
    pub unsafe fn new(base_address: PhysAddr) -> Self {
        Self { mmio: base::Mmio::new(base_address) }
    }

    /// Reads an u32 from the MMIO memory region.
    ///
    /// The offset is the number of u32-s (not byte offsets); that is, to read
    /// bytes at [base_address+4, base_address+8) the offset needs to be 1.
    ///
    /// Panics if the read would go outside the memory range.
    pub fn read_u32(&self, offset: usize) -> u32 {
        let offset = offset * size_of::<u32>();
        if offset >= S::SIZE as usize {
            panic!("invalid MMIO access for read: offset would read beyond memory boundary");
        }
        #[cfg(feature = "sev")]
        return sev::read_u32(&self.mmio, offset);
        #[cfg(not(feature = "sev"))]
        return self.mmio.read_u32(offset);
    }

    /// Write an u32 from the MMIO memory region.
    ///
    /// The offset is the number of u32-s (not byte offsets); that is, to read
    /// bytes at [base_address+4, base_address+8) the offset needs to be 1.
    ///
    /// Panics if the read would go outside the memory range.
    ///
    /// The caller needs to guarantee that the value is valid for the register
    /// it is written to.
    pub unsafe fn write_u32(&mut self, offset: usize, value: u32) {
        let offset = offset * size_of::<u32>();
        if offset >= S::SIZE as usize {
            panic!("invalid MMIO access for write: offset would write beyond memory boundary");
        }
        #[cfg(feature = "sev")]
        return sev::write_u32(&mut self.mmio, offset, value);
        #[cfg(not(feature = "sev"))]
        return self.mmio.write_u32(offset, value);
    }
}

/// Performs CPUID.
///
/// Under SEV-ES and above, you shouldn't call the CPUID instruction directly.
pub fn cpuid(leaf: u32) -> CpuidResult {
    #[cfg(feature = "sev")]
    return sev::cpuid(leaf);
    #[cfg(not(feature = "sev"))]
    return base::cpuid(leaf);
}
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

pub struct PortFactory;

#[cfg(feature = "sev")]
pub use sev::GhcbPortRead as PortRead;
#[cfg(feature = "sev")]
pub use sev::GhcbPortWrite as PortWrite;
#[cfg(not(feature = "sev"))]
pub use x86_64::structures::port::PortRead;
#[cfg(not(feature = "sev"))]
pub use x86_64::structures::port::PortWrite;

impl<'a, T> IoPortFactory<'a, T, Port<T>, Port<T>> for PortFactory
where
    T: PortRead + PortWrite + 'a,
{
    fn new_reader(&self, port: u16) -> Port<T> {
        Port::new(port)
    }

    fn new_writer(&self, port: u16) -> Port<T> {
        Port::new(port)
    }
}

/// Access to x86 IO ports.
pub struct Port<T> {
    port: u16,
    phantom: PhantomData<T>,
}

impl<T> Port<T> {
    pub fn new(port: u16) -> Self {
        Self { port, phantom: PhantomData }
    }
}

impl<T: PortRead> PortReader<T> for Port<T> {
    unsafe fn try_read(&mut self) -> Result<T, &'static str> {
        #[cfg(feature = "sev")]
        return <T as sev::GhcbPortRead>::read_from_port(self.port);
        #[cfg(not(feature = "sev"))]
        return Ok(<T as PortRead>::read_from_port(self.port));
    }
}

impl<T: PortWrite> PortWriter<T> for Port<T> {
    unsafe fn try_write(&mut self, value: T) -> Result<(), &'static str> {
        #[cfg(feature = "sev")]
        return <T as sev::GhcbPortWrite>::write_to_port(self.port, value);
        #[cfg(not(feature = "sev"))]
        return {
            <T as PortWrite>::write_to_port(self.port, value);
            Ok(())
        };
    }
}

/// Marks all memory of the VM as private and accepted.
///
/// The exact method is platform-specific, e.g. running PVALIDATE for SEV-SNP.
pub fn accept_memory(e820_table: &[BootE820Entry]) {
    #[cfg(feature = "sev")]
    sev::accept_memory(e820_table)
}
