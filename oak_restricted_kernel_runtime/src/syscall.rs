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

use crate::{raw_syscall::Syscall, syscall};
use core::ffi::{c_int, c_size_t, c_ssize_t, c_void};
use strum::{Display, FromRepr};

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug, Display, Eq, FromRepr, PartialEq)]
#[repr(isize)]
#[non_exhaustive]
pub enum Errno {
    /// Input/output error
    EIO = -5,
    /// Bad file descriptor
    EBADF = -9,
    /// Bad address
    EFAULT = -14,
    /// Invalid argument
    EINVAL = -22,
    /// Function not implemented
    ENOSYS = -38,
}

#[no_mangle]
pub extern "C" fn sys_read(fd: c_int, buf: *mut c_void, count: c_size_t) -> c_ssize_t {
    unsafe { syscall!(Syscall::Read, fd, buf, count) }
}

pub fn read(fd: i32, buf: *mut u8, len: usize) -> Result<usize, Errno> {
    let ret = sys_read(fd, buf as *mut c_void, len);

    if ret < 0 {
        Err(Errno::from_repr(ret)
            .unwrap_or_else(|| panic!("unexpected error from read syscall: {}", ret)))
    } else {
        Ok(ret as usize)
    }
}

#[no_mangle]
pub extern "C" fn sys_write(fd: c_int, buf: *const c_void, count: c_size_t) -> c_ssize_t {
    unsafe { syscall!(Syscall::Write, fd, buf, count) }
}

pub fn write(fd: i32, buf: *const u8, len: usize) -> Result<usize, Errno> {
    let ret = sys_write(fd, buf as *const c_void, len);

    if ret < 0 {
        Err(Errno::from_repr(ret)
            .unwrap_or_else(|| panic!("unexpected error from write syscall: {}", ret)))
    } else {
        Ok(ret as usize)
    }
}

#[no_mangle]
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

#[cfg(test)]
mod tests {
    extern crate std;
    use std::os::fd::AsRawFd;

    use super::*;

    #[test]
    fn test_read_write() {
        let (reader, writer) = os_pipe::pipe().unwrap();

        let tx = b"test";
        assert_eq!(Ok(4), write(writer.as_raw_fd(), tx.as_ptr(), tx.len()));

        let mut rx = [0u8; 4];
        assert_eq!(Ok(4), read(reader.as_raw_fd(), rx.as_mut_ptr(), rx.len()));

        assert_eq!(tx, &rx);
    }

    #[test]
    fn test_erroneus_read() {
        let fd = {
            let (reader, _) = os_pipe::pipe().unwrap();
            reader.as_raw_fd()
        };

        let mut rx = [0u8; 4];
        assert!(write(fd, rx.as_mut_ptr(), rx.len()).is_err());
    }

    #[test]
    fn test_erroneus_write() {
        let fd = {
            let (_, writer) = os_pipe::pipe().unwrap();
            writer.as_raw_fd()
        };

        let tx = b"test";
        assert!(write(fd, tx.as_ptr(), tx.len()).is_err());
    }

    #[test]
    fn test_fsync() {
        let fd = {
            let (_, writer) = os_pipe::pipe().unwrap();
            writer.as_raw_fd()
        };
        assert!(fsync(fd).is_err());
    }
}
