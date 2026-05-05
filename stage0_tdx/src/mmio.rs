//
// Copyright 2025 The Project Oak Authors
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
use oak_tdx_guest::vmcall::{mmio_read_u32, mmio_write_u32};
use x86_64::structures::paging::{PageSize, Size4KiB};

pub struct Mmio {}

impl oak_stage0::hal::Mmio for Mmio {
    fn read_u32(&self, offset: usize) -> u32 {
        let offset = offset * size_of::<u32>();
        if offset >= Size4KiB::SIZE as usize {
            panic!("invalid MMIO access for read: offset would read beyond memory boundary");
        }
        mmio_read_u32(offset as *const u32).unwrap()
    }

    unsafe fn write_u32(&mut self, offset: usize, val: u32) {
        let offset = offset * size_of::<u32>();
        if offset >= Size4KiB::SIZE as usize {
            panic!("invalid MMIO access for write: offset would write beyond memory boundary");
        }
        mmio_write_u32(offset as *mut u32, val).unwrap()
    }

    fn region_size(&self) -> usize {
        Size4KiB::SIZE as usize
    }
}
