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

use alloc::{
    boxed::Box,
    collections::{BTreeMap, btree_map::Entry},
    slice,
};
use core::{
    cmp::min,
    ffi::{c_int, c_size_t, c_ssize_t, c_void},
};

use oak_restricted_kernel_interface::Errno;
use spinning_top::Spinlock;

pub trait FileDescriptor: Send {
    fn read(&mut self, buf: &mut [u8]) -> Result<isize, Errno>;
    fn write(&mut self, buf: &[u8]) -> Result<isize, Errno>;
    fn sync(&mut self) -> Result<(), Errno>;
}

type Fd = c_int;

/// Utility function that copies the maximum number of bytes from a source
/// buffer to a destination buffer.
pub fn copy_max_slice(src_buf: &[u8], dst_buf: &mut [u8]) -> usize {
    let length: usize = min(src_buf.len(), dst_buf.len());
    dst_buf[..length].copy_from_slice(&src_buf[..length]);
    length
}

static FILE_DESCRIPTORS: Spinlock<BTreeMap<Fd, Box<dyn FileDescriptor>>> =
    Spinlock::new(BTreeMap::new());

/// Register a file descriptor.
///
/// This is kind of similar to what the "open" syscall would do, except that we
/// don't expose this to the user space and we don't allocate file descriptors.
///
/// Returns the FileDescriptor object back as an error if the fd is already in
/// use.
pub fn register(
    fd: Fd,
    descriptor: Box<dyn FileDescriptor>,
) -> Result<(), Box<dyn FileDescriptor>> {
    let mut descriptors = FILE_DESCRIPTORS.lock();

    if let Entry::Vacant(e) = descriptors.entry(fd) {
        e.insert(descriptor);
        Ok(())
    } else {
        Err(descriptor)
    }
}

/// Unregisters a file descriptor.
///
/// If the fd was registered, returns the FileDescriptor object backing it; if
/// the fd was unregistered, returns None.
#[allow(dead_code)]
pub fn unregister(fd: Fd) -> Option<Box<dyn FileDescriptor>> {
    FILE_DESCRIPTORS.lock().remove(&fd)
}

pub fn syscall_read(fd: c_int, buf: *mut c_void, count: c_size_t) -> c_ssize_t {
    // Safety: we should validate that the pointer and count are valid, as these
    // come from userspace and therefore are not to be trusted, but right now
    // everything is in kernel space so there is nothing to check.
    let data = unsafe { slice::from_raw_parts_mut(buf as *mut u8, count) };

    FILE_DESCRIPTORS
        .lock()
        .get_mut(&fd)
        .map(|channel| channel.read(data).unwrap_or_else(|err| err as isize))
        .unwrap_or(Errno::EBADF as isize)
}

pub fn syscall_write(fd: c_int, buf: *const c_void, count: c_size_t) -> c_ssize_t {
    // Safety: we should validate that the pointer and count are valid, as these
    // come from userspace and therefore are not to be trusted, but right now
    // everything is in kernel space so there is nothing to check.
    let data = unsafe { slice::from_raw_parts(buf as *mut u8, count) };

    FILE_DESCRIPTORS
        .lock()
        .get_mut(&fd)
        .map(|channel| channel.write(data).unwrap_or_else(|err| err as isize))
        .unwrap_or(Errno::EBADF as isize)
}

pub fn syscall_fsync(fd: c_int) -> c_ssize_t {
    FILE_DESCRIPTORS
        .lock()
        .get_mut(&fd)
        .map(|channel| channel.sync().map_or_else(|err| err as isize, |()| 0))
        .unwrap_or(Errno::EBADF as isize)
}
