//
// Copyright 2022 The Project Oak Authors
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

use x86_64::{
    align_down, align_up,
    structures::paging::{frame::PhysFrameRange, PageSize, PhysFrame, Size2MiB},
    PhysAddr,
};

pub struct Ramdisk {
    pub phys_addr: x86_64::PhysAddr,
    pub size: u64,
}

impl Ramdisk {
    pub fn phys_frame_range(&self) -> PhysFrameRange<Size2MiB> {
        PhysFrame::range(
            PhysFrame::<x86_64::structures::paging::Size2MiB>::from_start_address(PhysAddr::new(
                align_down(self.phys_addr.as_u64(), Size2MiB::SIZE),
            ))
            .unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(align_up(
                self.phys_addr.as_u64() + self.size,
                Size2MiB::SIZE,
            )))
            .unwrap(),
        )
    }
}
