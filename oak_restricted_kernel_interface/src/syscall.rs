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

use crate::{
    Errno, Syscall, syscall,
    syscalls::{MmapFlags, MmapProtection},
};

#[unsafe(no_mangle)]
pub extern "C" fn sys_read(fd: c_int, buf: *mut c_void, count: c_size_t) -> c_ssize_t {
    unsafe { syscall!(Syscall::Read, fd, buf, count) }
}

pub fn read(fd: i32, buf: &mut [u8]) -> Result<usize, Errno> {
    let ret = sys_read(fd, buf.as_mut_ptr() as *mut c_void, buf.len());

    if ret < 0 {
        Err(Errno::from_repr(ret)
            .unwrap_or_else(|| panic!("unexpected error from read syscall: {}", ret)))
    } else {
        Ok(ret as usize)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_write(fd: c_int, buf: *const c_void, count: c_size_t) -> c_ssize_t {
    unsafe { syscall!(Syscall::Write, fd, buf, count) }
}

pub fn write(fd: i32, buf: &[u8]) -> Result<usize, Errno> {
    let ret = sys_write(fd, buf.as_ptr() as *const c_void, buf.len());

    if ret < 0 {
        Err(Errno::from_repr(ret)
            .unwrap_or_else(|| panic!("unexpected error from write syscall: {}", ret)))
    } else {
        Ok(ret as usize)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_fsync(fd: c_int) -> c_ssize_t {
    unsafe { syscall!(Syscall::Fsync, fd) }
}

#[inline]
pub fn fsync(fd: i32) -> Result<(), Errno> {
    let ret = sys_fsync(fd);

    if ret < 0 {
        Err(Errno::from_repr(ret)
            .unwrap_or_else(|| panic!("unexpected error from fsync syscall: {}", ret)))
    } else {
        Ok(())
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_mmap(
    addr: *const c_void,
    size: c_size_t,
    prot: c_int,
    flags: c_int,
    fd: c_int,
    offset: c_int,
) -> isize {
    unsafe { syscall!(Syscall::Mmap, addr, size, prot, flags, fd, offset) }
}

pub fn mmap(
    addr: Option<*const c_void>,
    size: isize,
    prot: MmapProtection,
    flags: MmapFlags,
    fd: i32,
    offset: c_int,
) -> Result<&'static mut [u8], Errno> {
    let ret = sys_mmap(
        addr.unwrap_or(core::ptr::null()),
        size.try_into().map_err(|_| Errno::EINVAL)?,
        prot.bits(),
        flags.bits(),
        fd,
        offset,
    );

    if ret <= 0 {
        Err(Errno::from_repr(ret)
            .unwrap_or_else(|| panic!("unexpected error from mmap syscall: {}", ret)))
    } else {
        // Safety: if the syscall didn't return an error, then the kernel guarantees
        // that the address is valid and there is enough memory allocated.
        Ok(unsafe { core::slice::from_raw_parts_mut(ret as *mut u8, size as usize) })
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_exit(status: c_int) {
    unsafe { syscall!(Syscall::Exit, status) };
}

pub fn exit(status: i32) -> ! {
    sys_exit(status);
    unreachable!();
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_unstable_create_proccess(buf: *const c_void, count: c_size_t) -> c_ssize_t {
    unsafe { syscall!(Syscall::UnstableCreateProcess, buf, count) }
}

pub fn unstable_create_proccess(buf: &[u8]) -> Result<usize, Errno> {
    let ret = sys_unstable_create_proccess(buf.as_ptr() as *const c_void, buf.len());
    if ret <= 0 {
        Err(Errno::from_repr(ret).unwrap_or_else(|| {
            panic!("unexpected error from unstable_create_proccess syscall: {}", ret)
        }))
    } else {
        Ok(ret.try_into().expect("pid could not be represented as isize"))
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_unstable_switch_proccess(pid: c_size_t) -> c_ssize_t {
    unsafe { syscall!(Syscall::UnstableSwitchProcess, pid) }
}

pub fn unstable_switch_proccess(pid: usize) -> Result<usize, Errno> {
    let ret = sys_unstable_switch_proccess(pid);
    if ret < 0 {
        Err(Errno::from_repr(ret).unwrap_or_else(|| {
            panic!("unexpected error from unstable_switch_proccess syscall: {}", ret)
        }))
    } else {
        Ok(ret.try_into().expect("pid could not be represented as isize"))
    }
}

// Note that these tests are not being executed against Restricted Kernel, but
// rather the Linux kernel of the machine bazel is running on!
#[cfg(test)]
mod tests {
    extern crate std;
    use std::os::fd::AsRawFd;

    use super::*;

    #[test]
    fn test_read_write() {
        let (reader, writer) = os_pipe::pipe().unwrap();

        let tx = b"test";
        assert_eq!(Ok(4), write(writer.as_raw_fd(), tx));

        let mut rx = [0u8; 4];
        assert_eq!(Ok(4), read(reader.as_raw_fd(), &mut rx));

        assert_eq!(tx, &rx);
    }

    #[test]
    fn test_fsync() {
        let fd = {
            let (_, writer) = os_pipe::pipe().unwrap();
            writer.as_raw_fd()
        };
        assert!(fsync(fd).is_err());
    }

    #[test]
    fn test_mmap() {
        let mem = mmap(
            None,
            1024,
            MmapProtection::PROT_READ | MmapProtection::PROT_WRITE,
            MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE,
            -1,
            0,
        );
        assert!(mem.is_ok());
    }

    #[test]
    fn test_mmap_error() {
        let mem = mmap(
            None,
            0,
            MmapProtection::PROT_READ | MmapProtection::PROT_WRITE,
            MmapFlags::MAP_ANONYMOUS | MmapFlags::MAP_PRIVATE,
            -1,
            0,
        );
        assert!(mem.is_err());
    }
}
