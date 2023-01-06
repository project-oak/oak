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

use strum::FromRepr;

/// System calls implemented by Oak Restricted Kernel.
///
/// In general, the system calls are inpired by and look similar to the Linux/POSIX ABI, but we make
/// no claims about adhering to the behaviour, or specification, of either of those.
///
/// See <https://github.com/torvalds/linux/blob/master/arch/x86/entry/syscalls/syscall_64.tbl> for a
/// full list of system call numbers; we will ever only support a small subset of these.
#[repr(usize)]
#[derive(FromRepr)]
pub enum Syscall {
    /// Read from a file descriptor.
    ///
    /// Arguments:
    ///   - arg0 (c_ssize_t): file descriptor number
    ///   - arg1 (*mut c_void): pointer to the buffer to be filled
    ///   - arg2 (c_size_t): size of the buffer
    /// Returns:
    ///   a value of <errno::Errno> on failure; otherwise, the number of bytes read.
    Read = 0,

    /// Write to a file descriptor.
    ///
    /// Arguments:
    ///   - arg0 (c_ssize_t): file descriptor number
    ///   - arg1 (*const c_void): pointer to the buffer containing data to be written
    ///   - arg2 (c_size_t): size of the buffer
    /// Returns:
    ///   a value of <errno::Errno> on failure; otherwise, the number of bytes written.
    Write = 1,

    /// Flush a file descriptor.
    /// Arguments:
    ///   - arg0 (c_ssize_t): file descriptor number. Ignored by the kernel as we don't support
    ///     multiple file descriptors.
    /// Returns:
    ///   a value of <errno::Errno> on failure; 0, otherwise.
    Fsync = 74,
}
