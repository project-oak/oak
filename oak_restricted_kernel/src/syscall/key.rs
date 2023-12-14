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
use crate::DerivedKey;
use alloc::boxed::Box;
use oak_restricted_kernel_interface::{Errno, DERIVED_KEY_FD};

#[derive(Default)]
struct DerivedKeyDescriptor {
    key: DerivedKey,
    index: usize,
}

impl DerivedKeyDescriptor {
    fn new(key: DerivedKey) -> Self {
        Self { index: 0, key }
    }
}

impl FileDescriptor for DerivedKeyDescriptor {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        let length = copy_max_slice(&self.key[self.index..], buf);
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

/// Registers a file descriptor for reading a derived key (0x21)
pub fn register(key: DerivedKey) {
    super::fd::register(DERIVED_KEY_FD, Box::new(DerivedKeyDescriptor::new(key)))
        .map_err(|_| ()) // throw away the box
        .expect("DerivedKeyDescriptor already registered");
}
