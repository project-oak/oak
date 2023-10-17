//
// Copyright 2023 The Project Oak Authors
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

use super::fd::FileDescriptor;
use alloc::boxed::Box;
use core::cmp::min;
use oak_dice::evidence::RestrictedKernelDiceData as DiceData;
use oak_restricted_kernel_interface::{Errno, DICE_DATA_FD};

struct DiceDataDescriptor {
    data: DiceData,
}

impl FileDescriptor for DiceDataDescriptor {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        let data_as_bytes = <DiceData as zerocopy::AsBytes>::as_bytes(&self.data);
        let length = min(data_as_bytes.len(), buf.len());
        buf.copy_from_slice(&data_as_bytes[..length]);
        Ok(length as isize)
    }

    fn write(&mut self, _buf: &[u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        // Writing is not supported.
        Err(Errno::EINVAL)
    }

    fn sync(&mut self) -> Result<(), oak_restricted_kernel_interface::Errno> {
        Ok(())
    }
}

/// Registers a file descriptor for reading dice data
pub fn register(data: DiceData) {
    super::fd::register(DICE_DATA_FD, Box::new(DiceDataDescriptor { data }))
        .map_err(|_| ()) // throw away the box
        .expect("DiceDataDescriptor already registered");
}
