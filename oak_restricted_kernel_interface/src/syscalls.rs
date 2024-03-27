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

use bitflags::bitflags;
use strum::FromRepr;

/// Syscalls above this are unsafe, their behavior and availability cannot be
/// relied upon.
pub const UNSTABLE_SYSCALL_SPACE: usize = i32::MAX as usize - (10 ^ 3);

/// System calls implemented by Oak Restricted Kernel.
///
/// In general, the system calls are inpired by and look similar to the
/// Linux/POSIX ABI, but we make no claims about adhering to the behaviour, or
/// specification, of either of those.
///
/// See <https://github.com/torvalds/linux/blob/master/arch/x86/entry/syscalls/syscall_64.tbl> for a
/// full list of system call numbers; we will ever only support a small subset
/// of these.
#[repr(usize)]
#[derive(Debug, FromRepr)]
pub enum Syscall {
    /// Read from a file descriptor.
    ///
    /// Arguments:
    ///   - arg0 (c_ssize_t): file descriptor number
    ///   - arg1 (*mut c_void): pointer to the buffer to be filled
    ///   - arg2 (c_size_t): size of the buffer
    /// Returns:
    ///   a value of <errno::Errno> on failure; otherwise, the number of bytes
    /// read.
    Read = 0,

    /// Write to a file descriptor.
    ///
    /// Arguments:
    ///   - arg0 (c_ssize_t): file descriptor number
    ///   - arg1 (*const c_void): pointer to the buffer containing data to be
    ///     written
    ///   - arg2 (c_size_t): size of the buffer
    /// Returns:
    ///   a value of <errno::Errno> on failure; otherwise, the number of bytes
    /// written.
    Write = 1,

    /// Creates a mapping for memory.
    /// Arguments:
    ///   - arg0 (*const c_void): hint for start address for the new mapping,
    ///     may be nullptr
    ///   - arg1 (c_size_t): size of the new mapping
    ///   - arg2 (c_int): protection on mapping (PROT_EXEC, PROT_READ,
    ///     PROT_WRITE, PROT_NONE)
    ///   - arg3 (c_int): flags. We require MAP_PRIVATE and MAP_ANONYMOUS to be
    ///     set, and additionally support MAP_FIXED.
    ///   - arg4 (c_int): file descriptor. Ignored, as we only support anonymous
    ///     mappings. Should be set to -1 by caller.
    ///   - arg5 (c_int): offset. Ignored, as we only support anonymous
    ///     mappings. Should be set to 0 by caller.
    /// Oak Restricted Kernel considerations:
    ///   - our mmap will work on 2 MiB chunks; even if size is 1 byte, we will
    ///     reserve a 2 MiB chunk of memory. Thus, size should be kept as a
    ///     multiple of 2 MiB.
    ///   - related to previous, the allocation address will always be 2
    ///     MiB-aligned (rounded upward from hint).
    ///   - MAP_FIXED requires address to be 2 MiB-aligned, and will return an
    ///     error if it'd touch any existing mappings.
    ///   - We do not support PROT_NONE; PROT_READ is always implied.
    Mmap = 9,

    /// Terminates he calling process.
    /// Arguments:
    ///   - arg0 (c_int): error code
    /// Oak Restricted Kernel considerations:
    ///   We don't expect the user process to terminate, so this triggers a
    /// kernel panic, no matter   the error code.
    Exit = 60,

    /// Flush a file descriptor.
    /// Arguments:
    ///   - arg0 (c_ssize_t): file descriptor number. Ignored by the kernel as
    ///     we don't support multiple file descriptors.
    /// Returns:
    ///   a value of <errno::Errno> on failure; 0, otherwise.
    Fsync = 74,

    /// Create new process from ELF file, without starting it.
    ///
    /// Arguments:
    ///   - arg0 (*mut c_void): pointer to the a buffer holding an ELF file
    ///   - arg1 (c_size_t): size of the buffer
    /// Returns:
    ///   a value of <errno::Errno> on failure; Otherwise the PID of the new
    /// process.
    UnstableCreateProcess = UNSTABLE_SYSCALL_SPACE,

    /// Switch the active execution execution to the process with the provided
    /// PID.
    ///
    /// Arguments:
    ///   - arg0 (c_size_t): PID of the process.
    /// Returns:
    ///   a value of <errno::Errno> on failure; 0, otherwise.
    UnstableSwitchProcess = UNSTABLE_SYSCALL_SPACE + 1,
}

bitflags! {
    #[repr(C)]
    pub struct MmapProtection: i32 {
        /// Pages may be read.
        const PROT_READ = 0x1;

        // Pages may be written.
        const PROT_WRITE = 0x2;

        /// Pages may be executed.
        const PROT_EXEC = 0x4;
    }
}

bitflags! {
    #[derive(Debug)]
    #[repr(C)]
    pub struct MmapFlags: i32 {
        /// Private copy-on-write mapping.
        const MAP_PRIVATE = 0x02;

        /// Don't interpret addr as a hint, but require mapping at given address.
        const MAP_FIXED = 0x10;

        /// The mapping is not backed by any file; contents are initialized to zero.
        const MAP_ANONYMOUS = 0x20;
    }
}
