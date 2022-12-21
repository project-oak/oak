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
    EIO = -9,     // Input/output error
    EFAULT = -14, // Bad address
}

#[no_mangle]
pub extern "C" fn sys_read(fd: c_int, buf: *mut c_void, count: c_size_t) -> c_ssize_t {
    unsafe { syscall!(Syscall::Read, fd, buf, count) }
}

pub fn read(fd: i32, buf: *mut u8, len: usize) -> Result<usize, Errno> {
    let ret = sys_read(fd, buf as *mut c_void, len);

    if ret < 0 {
        Err(Errno::from_repr(ret)
            .unwrap_or_else(|| panic!("unexpected error from READ syscall: {}", ret)))
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
            .unwrap_or_else(|| panic!("unexpected error from WRITE syscall: {}", ret)))
    } else {
        Ok(ret as usize)
    }
}

#[no_mangle]
pub extern "C" fn sys_sync() {
    unsafe { syscall!(Syscall::Sync) };
}

#[inline]
pub fn sync() {
    sys_sync()
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
        assert_eq!(
            Ok(4),
            write(writer.as_raw_fd() as i32, tx.as_ptr(), tx.len())
        );

        let mut rx = [0u8; 4];
        assert_eq!(
            Ok(4),
            read(reader.as_raw_fd() as i32, rx.as_mut_ptr(), rx.len())
        );

        assert_eq!(tx, &rx);
    }

    #[test]
    fn test_erroneus_read() {
        let fd = {
            let (reader, _) = os_pipe::pipe().unwrap();
            reader.as_raw_fd() as i32
        };

        let mut rx = [0u8; 4];
        assert_eq!(Err(Errno::EIO), write(fd, rx.as_mut_ptr(), rx.len()));
    }

    #[test]
    fn test_erroneus_write() {
        let fd = {
            let (_, writer) = os_pipe::pipe().unwrap();
            writer.as_raw_fd() as i32
        };

        let tx = b"test";
        assert_eq!(Err(Errno::EIO), write(fd, tx.as_ptr(), tx.len()));
    }

    #[test]
    fn test_sync() {
        // Not that we can tell if anything goes wrong...
        sync();
    }
}
