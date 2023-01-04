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

use core::ffi::{c_int, c_size_t, c_ssize_t, c_void};

use alloc::{boxed::Box, slice};
use oak_channel::Channel;
use oak_core::sync::OnceCell;
use oak_restricted_kernel_interface::Errno;
use spinning_top::Spinlock;

trait FileDescriptor {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, Errno>;
    fn write(&mut self, buf: &[u8]) -> Result<isize, Errno>;
    fn sync(&mut self) -> Result<(), Errno>;
}

#[repr(transparent)]
struct ChannelDescriptor {
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
        self.channel.read(buf).map_err(|_| Errno::EIO).map(|_| size)
    }

    fn write(&mut self, buf: &[u8]) -> Result<isize, Errno> {
        let size: isize = buf.len().try_into().map_err(|_| Errno::EINVAL)?;
        self.channel
            .write(buf)
            .map_err(|_| Errno::EIO)
            .map(|_| size)
    }

    fn sync(&mut self) -> Result<(), Errno> {
        self.channel.flush().map_err(|_| Errno::EIO)
    }
}

static CHANNEL_DESCRIPTOR: OnceCell<Spinlock<ChannelDescriptor>> = OnceCell::new();

pub fn init(channel: Box<dyn Channel>) {
    CHANNEL_DESCRIPTOR
        .set(Spinlock::new(ChannelDescriptor::new(channel)))
        .map_err(|_| ())
        .expect("communication channel was already initialised");
}

pub fn syscall_read(_fd: c_int, buf: *mut c_void, count: c_size_t) -> c_ssize_t {
    // We should validate that the pointer and count are valid, as these come from userspace and
    // therefore are not to be trusted, but right now everything is in kernel space so there is
    // nothing to check.
    let data = unsafe { slice::from_raw_parts_mut(buf as *mut u8, count) };

    let mut channel = CHANNEL_DESCRIPTOR
        .get()
        .expect("syscall interface not ready yet")
        .lock();
    channel.read(data).unwrap_or_else(|err| err as isize)
}

pub fn syscall_write(_fd: c_int, buf: *const c_void, count: c_size_t) -> c_ssize_t {
    // We should validate that the pointer and count are valid, as these come from userspace and
    // therefore are not to be trusted, but right now everything is in kernel space so there is
    // nothing to check.
    let data = unsafe { slice::from_raw_parts(buf as *mut u8, count) };

    let mut channel = CHANNEL_DESCRIPTOR
        .get()
        .expect("syscall interface not ready yet")
        .lock();
    channel.write(data).unwrap_or_else(|err| err as isize)
}

pub fn syscall_fsync(_fd: c_int) -> c_ssize_t {
    let mut channel = CHANNEL_DESCRIPTOR
        .get()
        .expect("syscall interface not ready yet")
        .lock();
    channel
        .sync()
        .map(|()| 0)
        .unwrap_or_else(|err| err as isize)
}
