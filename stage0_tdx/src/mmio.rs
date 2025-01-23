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

pub struct Mmio {}

impl<S: x86_64::structures::paging::page::PageSize> oak_stage0::hal::Mmio<S> for Mmio {
    fn read_u32(&self, offset: usize) -> u32 {
        mmio_read_u32(offset as *const u32).unwrap()
    }
    unsafe fn write_u32(&mut self, offset: usize, val: u32) {
        mmio_write_u32(offset as *mut u32, val).unwrap()
    }
}
