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

use core::mem::size_of;

use oak_stage0::hal::base::Mmio as BaseMmio;
use x86_64::PhysAddr;

use super::GHCB_WRAPPER;

pub struct Mmio {
    mmio: BaseMmio,
}

impl Mmio {
    /// # Safety
    ///
    /// The caller must ensure that the base address is the start of a valid
    /// 4KiB MMIO region.
    pub unsafe fn new(base_address: PhysAddr, size: usize) -> Self {
        Self { mmio: unsafe { BaseMmio::new(base_address, size) } }
    }
}

impl oak_stage0::hal::Mmio for Mmio {
    fn read_u32(&self, offset: usize) -> u32 {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            let offset = offset * size_of::<u32>();
            if offset >= self.mmio.layout.size() {
                panic!("invalid MMIO access for read: offset would read beyond memory boundary");
            }
            ghcb.mmio_read_u32(self.mmio.base_address + (offset as u64))
                .expect("couldn't read the MSR using the GHCB protocol")
        } else {
            self.mmio.read_u32(offset)
        }
    }

    unsafe fn write_u32(&mut self, offset: usize, value: u32) {
        if let Some(mut ghcb) = GHCB_WRAPPER.get() {
            let offset = offset * size_of::<u32>();
            if offset >= self.mmio.layout.size() {
                panic!("invalid MMIO access for write: offset would write beyond memory boundary");
            }
            ghcb.mmio_write_u32(self.mmio.base_address + (offset as u64), value)
                .expect("couldn't read the MSR using the GHCB protocol")
        } else {
            unsafe { self.mmio.write_u32(offset, value) }
        }
    }

    fn region_size(&self) -> usize {
        self.mmio.region_size()
    }
}
