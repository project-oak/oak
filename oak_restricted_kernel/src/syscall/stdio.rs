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

use alloc::boxed::Box;
use core::cmp::min;

use oak_restricted_kernel_interface::Errno;

use super::fd::FileDescriptor;
use crate::logging::SERIAL1;

#[derive(Default)]
struct Stderr {}

impl FileDescriptor for Stderr {
    fn read(&mut self, _buf: &mut [u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        Err(Errno::EINVAL)
    }

    fn write(&mut self, buf: &[u8]) -> Result<isize, oak_restricted_kernel_interface::Errno> {
        // buf may be up to usize, but we need to return the number of bytes as isize.
        // Let's follow the Linux example of only writing up to isize::MAX
        // bytes.
        let buf = &buf[..min(buf.len(), isize::MAX as usize)];
        let mut lock = SERIAL1.lock();
        let port = lock.as_mut().unwrap();
        for &byte in buf {
            // We don't log the error, as (a) we're holding the mutex on the serial port so
            // logging wouldn't work, and (b) it's the write to the serial port
            // that failed, and our logs would go over the exact same serial
            // port so writing the log would likely fail as well.
            port.send(byte).map_err(|_| Errno::EIO)?;
        }
        Ok(buf.len() as isize)
    }

    fn sync(&mut self) -> Result<(), oak_restricted_kernel_interface::Errno> {
        Ok(())
    }
}

/// Registers a file descriptor for stderr (2)
pub fn register() {
    super::fd::register(2, Box::<Stderr>::default())
        .map_err(|_| ()) // throw away the box
        .expect("stderr already registered");
}
