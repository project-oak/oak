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

use oak_hal::Mmio as HalMmio;
use x86_64::{PhysAddr, VirtAddr};

/// An MMIO implementation that supports both direct volatile access and
/// GHCB-based access.
///
/// This implements [`oak_hal::Mmio`] by performing volatile reads and writes to
/// a virtual memory region, or by using the GHCB protocol for SEV-ES and
/// SEV-SNP guests.
pub struct SevMmio {
    /// Virtual address of the MMIO region base. Used for direct volatile
    /// access.
    base_virt: VirtAddr,
    /// Physical address of the MMIO region base. Used for GHCB-based access.
    base_phys: PhysAddr,
    /// Size of the MMIO region in bytes.
    size: usize,
    /// Whether to use GHCB for MMIO access.
    use_ghcb: bool,
}

impl SevMmio {
    /// Creates a new `SevMmio` for the given addresses and size.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `base_virt` points to a valid MMIO region of
    /// at least `size` bytes that is mapped in the page tables and will
    /// remain valid for the lifetime of this struct.
    pub unsafe fn new(
        base_virt: VirtAddr,
        base_phys: PhysAddr,
        size: usize,
        use_ghcb: bool,
    ) -> Self {
        Self { base_virt, base_phys, size, use_ghcb }
    }
}

impl HalMmio for SevMmio {
    fn read_u32(&self, offset: usize) -> u32 {
        let byte_offset = offset * size_of::<u32>();
        assert!(
            byte_offset + size_of::<u32>() <= self.size,
            "MMIO read at offset {offset} (byte {byte_offset}) exceeds region size {}",
            self.size
        );
        if self.use_ghcb {
            let mut ghcb = crate::ghcb::GHCB_PROTOCOL.get().expect("GHCB not initialized").lock();
            ghcb.mmio_read_u32(self.base_phys + (byte_offset as u64))
                .expect("couldn't read MMIO using the GHCB protocol")
        } else {
            // Safety: the caller of `SevMmio::new` guaranteed the region is
            // valid and mapped. The assertion above ensures we stay in bounds.
            unsafe { (self.base_virt.as_u64() as *const u32).add(offset).read_volatile() }
        }
    }

    unsafe fn write_u32(&mut self, offset: usize, value: u32) {
        let byte_offset = offset * size_of::<u32>();
        assert!(
            byte_offset + size_of::<u32>() <= self.size,
            "MMIO write at offset {offset} (byte {byte_offset}) exceeds region size {}",
            self.size
        );
        if self.use_ghcb {
            let mut ghcb = crate::ghcb::GHCB_PROTOCOL.get().expect("GHCB not initialized").lock();
            ghcb.mmio_write_u32(self.base_phys + (byte_offset as u64), value)
                .expect("couldn't write MMIO using the GHCB protocol")
        } else {
            // Safety: the caller of `SevMmio::new` guaranteed the region is
            // valid and mapped, and the caller of `write_u32` guarantees the
            // value is valid for the register.
            unsafe { (self.base_virt.as_u64() as *mut u32).add(offset).write_volatile(value) };
        }
    }

    fn region_size(&self) -> usize {
        self.size
    }
}
