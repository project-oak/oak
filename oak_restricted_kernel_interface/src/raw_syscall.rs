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

use core::arch::asm;

use crate::Syscall;

/// Invoke system calls based on the Linux calling convention using `SYSCALL`.
///
/// See <https://github.com/torvalds/linux/blob/master/arch/x86/entry/calling.h> for the definition
/// of the calling convention, and the AMD64 Architecture Programmer's Manual,
/// Volume 3 for the semantics of `SYSCALL`/`SYSRET`.
#[macro_export]
macro_rules! syscall {
    ($syscall:expr) => {
        $crate::raw_syscall::syscall0($syscall)
    };
    ($syscall:expr, $arg1:expr) => {
        $crate::raw_syscall::syscall1($syscall, $arg1 as usize)
    };
    ($syscall:expr, $arg1:expr, $arg2:expr) => {
        $crate::raw_syscall::syscall2($syscall, $arg1 as usize, $arg2 as usize)
    };
    ($syscall:expr, $arg1:expr, $arg2:expr, $arg3:expr) => {
        $crate::raw_syscall::syscall3($syscall, $arg1 as usize, $arg2 as usize, $arg3 as usize)
    };
    ($syscall:expr, $arg1:expr, $arg2:expr, $arg3:expr, $arg4:expr, $arg5:expr, $arg6:expr) => {
        $crate::raw_syscall::syscall6(
            $syscall,
            $arg1 as usize,
            $arg2 as usize,
            $arg3 as usize,
            $arg4 as usize,
            $arg5 as usize,
            $arg6 as usize,
        )
    };
}

#[inline]
#[allow(dead_code)]
pub unsafe fn syscall0(syscall: Syscall) -> isize {
    let mut ret: isize;
    unsafe {
        asm!("syscall",
             out("rcx") _,
             out("r11") _,
             inout("rax") syscall as u64 => ret);
    }
    ret
}

#[inline]
pub unsafe fn syscall1(syscall: Syscall, arg1: usize) -> isize {
    let mut ret: isize;
    unsafe {
        asm!("syscall",
             in("rdi") arg1,
             out("rcx") _,
             out("r11") _,
             inout("rax") syscall as u64 => ret);
    }
    ret
}

#[inline]
#[allow(dead_code)]
pub unsafe fn syscall2(syscall: Syscall, arg1: usize, arg2: usize) -> isize {
    let mut ret: isize;
    unsafe {
        asm!("syscall",
             in("rdi") arg1,
             in("rsi") arg2,
             out("rcx") _,
             out("r11") _,
             inout("rax") syscall as u64 => ret);
    }
    ret
}

#[inline]
pub unsafe fn syscall3(syscall: Syscall, arg1: usize, arg2: usize, arg3: usize) -> isize {
    let mut ret: isize;
    unsafe {
        asm!("syscall",
             in("rdi") arg1,
             in("rsi") arg2,
             in("rdx") arg3,
             out("rcx") _,
             out("r11") _,
             inout("rax") syscall as u64 => ret);
    }
    ret
}

#[inline]
pub unsafe fn syscall6(
    syscall: Syscall,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    arg4: usize,
    arg5: usize,
    arg6: usize,
) -> isize {
    let mut ret: isize;
    unsafe {
        asm!("syscall",
             in("rdi") arg1,
             in("rsi") arg2,
             in("rdx") arg3,
             in("r10") arg4,
             in("r8") arg5,
             in("r9") arg6,
             out("rcx") _,
             out("r11") _,
             inout("rax") syscall as u64 => ret);
    }
    ret
}
