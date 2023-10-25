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

use super::fd::{copy_max_slice, FileDescriptor};
use alloc::boxed::Box;
use oak_dice::evidence::RestrictedKernelDiceData as DiceData;
use oak_restricted_kernel_interface::{Errno, DICE_DATA_FD};

struct DiceDataDescriptor {
    data: DiceData,
    index: usize,
}

impl DiceDataDescriptor {
    fn new(data: DiceData) -> Self {
        Self { index: 0, data }
    }
}

impl FileDescriptor for DiceDataDescriptor {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        let data_as_slice = <DiceData as zerocopy::AsBytes>::as_bytes_mut(&mut self.data);
        let length = copy_max_slice(&data_as_slice[self.index..], buf);

        // destroy the data that was read, to ensure that it can only be read once
        let slice_to_read = &mut data_as_slice[self.index..(self.index + length)];
        slice_to_read.fill(0);

        self.index += length;
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
    super::fd::register(DICE_DATA_FD, Box::new(DiceDataDescriptor::new(data)))
        .map_err(|_| ()) // throw away the box
        .expect("DiceDataDescriptor already registered");
}
