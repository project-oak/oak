//
// Copyright 2026 The Project Oak Authors
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

use core::arch::x86_64::CpuidResult;

use oak_hal::{PageAssignment, Platform, PortFactory};
use oak_restricted_kernel::PAGE_TABLES;
use x86_64::{
    PhysAddr,
    structures::{
        mem_encrypt::{MemoryEncryptionConfiguration, enable_memory_encryption},
        paging::{Mapper, Page, PhysFrame, Size4KiB},
    },
};

pub struct TdxMmio {
    base_phys: PhysAddr,
    size: usize,
}

impl TdxMmio {
    /// Creates a new `TdxMmio` instance.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the base address and size point to a valid
    /// physical memory-mapped I/O region.
    pub unsafe fn new(base_phys: PhysAddr, size: usize) -> Self {
        Self { base_phys, size }
    }
}

impl oak_hal::Mmio for TdxMmio {
    fn read_u32(&self, offset: usize) -> u32 {
        let byte_offset = offset * size_of::<u32>();
        assert!(
            byte_offset + size_of::<u32>() <= self.size,
            "MMIO read at offset {offset} (byte {byte_offset}) exceeds region size {}",
            self.size
        );
        let phys_addr = self.base_phys.as_u64() + byte_offset as u64;
        oak_tdx_guest::vmcall::mmio_read_u32(phys_addr as *const u32)
            .expect("failed to read MMIO via TDVMCALL")
    }

    unsafe fn write_u32(&mut self, offset: usize, value: u32) {
        let byte_offset = offset * size_of::<u32>();
        assert!(
            byte_offset + size_of::<u32>() <= self.size,
            "MMIO write at offset {offset} (byte {byte_offset}) exceeds region size {}",
            self.size
        );
        let phys_addr = self.base_phys.as_u64() + byte_offset as u64;
        // Safety: the caller guarantees the value is valid for the register, and that
        // the address is a valid MMIO register.
        oak_tdx_guest::vmcall::mmio_write_u32(phys_addr as *mut u32, value)
            .expect("failed to write MMIO via TDVMCALL");
    }

    fn region_size(&self) -> usize {
        self.size
    }
}

pub struct Tdx {}

impl Platform for Tdx {
    type Mmio = TdxMmio;

    fn cpuid(leaf: u32) -> CpuidResult {
        oak_tdx_guest::vmcall::call_cpuid(leaf, 0).expect("failed to call CPUID")
    }

    /// # Safety
    ///
    /// The caller must ensure that the base address and the size represents a
    /// valid MMIO region.
    unsafe fn mmio(base_address: PhysAddr, size: usize) -> Self::Mmio {
        // Safety: The caller must ensure that the physical MMIO base address and size
        // are valid.
        unsafe { TdxMmio::new(base_address, size) }
    }

    fn port_factory() -> PortFactory {
        PortFactory {
            read_u8: |port| oak_tdx_guest::vmcall::io_read_u8(port as u32),
            read_u16: |port| oak_tdx_guest::vmcall::io_read_u16(port as u32),
            read_u32: |port| oak_tdx_guest::vmcall::io_read_u32(port as u32),
            write_u8: |port, value| oak_tdx_guest::vmcall::io_write_u8(port as u32, value),
            write_u16: |port, value| oak_tdx_guest::vmcall::io_write_u16(port as u32, value),
            write_u32: |port, value| oak_tdx_guest::vmcall::io_write_u32(port as u32, value),
        }
    }

    fn early_initialize_platform() {}

    fn change_frame_state(frame: PhysFrame<Size4KiB>, state: PageAssignment) {
        let range = PhysFrame::range(frame, frame + 1);
        // Safety: mapping a GPA is safe if the caller maps it correctly in the page
        // tables.
        unsafe {
            oak_tdx_guest::vmcall::map_gpa(range, state).expect("failed to map GPA");
        }
    }

    fn revalidate_page(page: Page<Size4KiB>) {
        let mut pt_guard = PAGE_TABLES.lock();
        let mapper = pt_guard.get_mut().unwrap();
        let frame = mapper.translate_page(page).expect("failed to translate page");
        oak_tdx_guest::tdcall::accept_memory(frame).expect("failed to accept memory");
    }

    fn wbvind() {
        oak_tdx_guest::vmcall::tdvmcall_wbinvd().expect("failed to execute WBINVD");
    }

    fn init_memory_encryption() -> bool {
        let shared_bit = (oak_tdx_guest::tdcall::get_td_info().gpa_width - 1) as u8;
        // Safety: all relevant page tables must be updated after this is set.
        unsafe {
            enable_memory_encryption(MemoryEncryptionConfiguration::SharedBit(shared_bit));
        }
        true
    }

    fn is_memory_encryption_enabled() -> bool {
        true
    }
}

impl oak_hal::MsrAccess for Tdx {
    unsafe fn read_msr(msr: u32) -> u64 {
        // Safety: The caller must guarantee that the MSR is valid.
        oak_tdx_guest::vmcall::msr_read(msr).expect("failed to read MSR")
    }

    unsafe fn write_msr(msr: u32, value: u64) {
        // Safety: The caller must guarantee that the MSR is valid.
        unsafe { oak_tdx_guest::vmcall::msr_write(msr, value).expect("failed to write MSR") }
    }
}

impl oak_restricted_kernel::hal::KernelPlatform for Tdx {
    fn initialize_platform(_info: &oak_linux_boot_params::BootParams) {}

    fn add_additional_interrupt_handlers(
        _idt: &mut x86_64::structures::idt::InterruptDescriptorTable,
    ) {
    }

    fn shutdown() -> ! {
        oak_restricted_kernel::shutdown::shutdown_with_port_factory(&Self::port_factory())
    }
}
