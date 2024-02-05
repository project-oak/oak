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

//! Provides functionality to communicate with host application over the communication channel.

use anyhow::anyhow;
pub use oak_channel::{server::start_blocking_server, Read, Write};
use oak_restricted_kernel_interface::OAK_CHANNEL_FD;

/// Channel that communicates over a file descriptor.
pub struct FileDescriptorChannel {
    fd: i32,
}

impl FileDescriptorChannel {
    pub fn new(fd: i32) -> Self {
        Self { fd }
    }
}

impl Default for FileDescriptorChannel {
    /// Constructs a new FileDescriptorChannel that assumes we'll use the well-known Oak file
    /// descriptor number.
    fn default() -> Self {
        Self::new(OAK_CHANNEL_FD)
    }
}

impl Read for FileDescriptorChannel {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let len = data.len();
        let mut remaining = data.len();

        while remaining > 0 {
            remaining -= oak_restricted_kernel_interface::syscall::read(
                self.fd,
                &mut data[len - remaining..],
            )
            .map_err(|err| anyhow!("read failure: {}", err))?;
        }

        Ok(())
    }
}

impl Write for FileDescriptorChannel {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let len = data.len();
        let mut remaining = data.len();

        while remaining > 0 {
            remaining -=
                oak_restricted_kernel_interface::syscall::write(self.fd, &data[len - remaining..])
                    .map_err(|err| anyhow!("write failure: {}", err))?;
        }

        Ok(())
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        oak_restricted_kernel_interface::syscall::fsync(self.fd)
            .map_err(|err| anyhow!("sync failure: {}", err))
    }
}
