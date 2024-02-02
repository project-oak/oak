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

use oak_channel_core::Channel;
use oak_restricted_kernel_interface::{Errno, OAK_CHANNEL_FD};

use super::fd::FileDescriptor;

#[repr(transparent)]
pub struct ChannelDescriptor {
    channel: Box<dyn Channel>,
}

impl ChannelDescriptor {
    pub fn new(channel: Box<dyn Channel>) -> Self {
        Self { channel }
    }
}

impl FileDescriptor for ChannelDescriptor {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, Errno> {
        let size: isize = buf.len().try_into().map_err(|_| Errno::EINVAL)?;
        self.channel
            .read_exact(buf)
            .map_err(|_| Errno::EIO)
            .map(|_| size)
    }

    fn write(&mut self, buf: &[u8]) -> Result<isize, Errno> {
        let size: isize = buf.len().try_into().map_err(|_| Errno::EINVAL)?;
        self.channel
            .write_all(buf)
            .map_err(|_| Errno::EIO)
            .map(|_| size)
    }

    fn sync(&mut self) -> Result<(), Errno> {
        self.channel.flush().map_err(|_| Errno::EIO)
    }
}

/// Registers a handler for the Oak communication channel file descriptor (`oak_channel_core_FD`)
pub fn register(channel: Box<dyn Channel>) {
    super::fd::register(OAK_CHANNEL_FD, Box::new(ChannelDescriptor::new(channel)))
        .map_err(|_| ()) // throw away the box we get back
        .expect("communication channel was already registered");
}
