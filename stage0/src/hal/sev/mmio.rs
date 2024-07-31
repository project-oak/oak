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

use x86_64::structures::paging::PageSize;

use crate::{hal::base::Mmio, sev::GHCB_WRAPPER};

pub fn read_u32<S: PageSize>(mmio: &Mmio<S>, offset: usize) -> u32 {
    if let Some(mut ghcb) = GHCB_WRAPPER.get() {
        ghcb.mmio_read_u32(mmio.base_address + offset)
            .expect("couldn't read the MSR using the GHCB protocol")
    } else {
        mmio.read_u32(offset)
    }
}

pub unsafe fn write_u32<S: PageSize>(mmio: &mut Mmio<S>, offset: usize, value: u32) {
    if let Some(mut ghcb) = GHCB_WRAPPER.get() {
        ghcb.mmio_write_u32(mmio.base_address + offset, value)
            .expect("couldn't read the MSR using the GHCB protocol")
    } else {
        mmio.write_u32(offset, value)
    }
}
