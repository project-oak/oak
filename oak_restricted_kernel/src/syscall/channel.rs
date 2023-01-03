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

use alloc::{boxed::Box, collections::BTreeMap, rc::Rc, slice, sync::Arc};
use core::{
    any::Any,
    ffi::{c_size_t, c_ssize_t, c_void},
};
use oak_channel::Channel;
use oak_core::sync::OnceCell;
use oak_restricted_kernel_runtime::syscall::Errno;
use spinning_top::Spinlock;

trait FileDescriptor {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, Errno>;
    fn write(&mut self, buf: &[u8]) -> Result<isize, Errno>;
    fn sync(&mut self) -> Result<(), Errno>;
}

struct Stderr {}
impl FileDescriptor for Stderr {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, Errno> {
        Err(Errno::EBADF)
    }

    fn write(&mut self, buf: &[u8]) -> Result<isize, Errno> {
        let size: isize = buf.len().try_into().map_err(|_| Errno::EINVAL)?;
        log::info!("{:?}", buf);
        Ok(size)
    }

    fn sync(&mut self) -> Result<(), Errno> {
        Ok(())
    }
}

#[repr(transparent)]
struct ChannelDescriptor {
    channel: Box<dyn Channel>,
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

struct DescriptorMap {
    descriptors: BTreeMap<isize, Arc<dyn FileDescriptor>>,
}

impl DescriptorMap {
    pub fn add(&mut self, fd: isize, descriptor: Box<dyn FileDescriptor>) {}
}

/*
static DESCRIPTORS: OnceCell<BTreeMap<isize, Arc<Spinlock<dyn FileDescriptor>>>> = OnceCell::new();
*/
pub fn init(channel: Box<dyn Channel>) {
    /*
    let mut map: BTreeMap<isize, Box<dyn FileDescriptor + Send + Sync>> = BTreeMap::new();
    map.insert(10, Box::new(ChannelDescriptor { channel }));
    map.insert(3, Box::new(Stderr {}));
    DESCRIPTORS.set(map);
    */
    /*
    CHANNEL
        .set(channel)
        .map_err(|_| ())
        .expect("communication channel was already initialised");
    */
}

/*
pub fn syscall_read(buf: *mut c_void, count: c_size_t) -> c_ssize_t {
    let data = unsafe { slice::from_raw_parts_mut(buf as *mut u8, count) };
    let result = CHANNEL
        .get()
        .expect("syscall interface not ready yet")
        .read(data);

    count.try_into().unwrap()
}
pub fn syscall_write() {}
pub fn syscall_sync() {}
*/
