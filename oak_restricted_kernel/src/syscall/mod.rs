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

mod channel;
pub mod dice_data;
mod fd;
mod key;
pub mod mmap;
mod process;
mod stdio;

mod switch_process;

#[cfg(test)]
mod tests;

use alloc::boxed::Box;
use core::{arch::asm, ffi::c_void};

use oak_channel::Channel;
use oak_restricted_kernel_interface::{Errno, Syscall};
use x86_64::{
    registers::{
        control::Efer,
        model_specific::{EferFlags, GsBase, KernelGsBase, LStar},
    },
    VirtAddr,
};

use self::{
    fd::{syscall_fsync, syscall_read, syscall_write},
    mmap::syscall_mmap,
    process::syscall_exit,
    switch_process::syscall_unstable_switch_proccess,
};
use crate::mm;

/// State we need to track for system calls.
///
/// Do not change the order of the fields here, as this is accessed from
/// assembly!
#[repr(C)]
#[derive(Debug)]
struct GsData {
    /// Kernel stack pointer (what to set in RSP after saving user RSP).
    kernel_sp: VirtAddr,

    /// User stack pointer. Saved from RSP after SYSCALL.
    user_sp: VirtAddr,

    /// User instruction pointer (where to return after SYSCALL). Saved from
    /// RCX.
    user_ip: VirtAddr,

    /// User flags. Saved from R11.
    user_flags: usize,
}

pub fn enable_syscalls(channel: Box<dyn Channel>, dice_data: dice_data::DiceData) {
    channel::register(channel);
    stdio::register();
    key::register();
    dice_data::register(dice_data);

    // Allocate a stack for the system call handler.
    let kernel_sp = mm::allocate_stack();

    // Store the gsdata structure in the kernel heap.
    // We need the GsData to stick around statically, so we'll leak it here.
    let gsdata = Box::leak(Box::new(GsData {
        // Stack grows down, so SP points to the end of the page
        kernel_sp,
        user_sp: VirtAddr::zero(),
        user_ip: VirtAddr::zero(),
        user_flags: 0,
    }));

    KernelGsBase::write(VirtAddr::from_ptr(gsdata));
    GsBase::write(VirtAddr::from_ptr(gsdata));

    LStar::write(VirtAddr::new(syscall_entrypoint as usize as u64));
    unsafe {
        Efer::update(|flags| flags.set(EferFlags::SYSTEM_CALL_EXTENSIONS, true));
    }
}

/// Rust wrapper for system calls.
///
/// This function assumes the 64-bit SysV ABI, not the syscall ABI!
extern "sysv64" fn syscall_handler(
    syscall: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    arg4: usize,
    arg5: usize,
    arg6: usize,
) -> isize {
    // SysV ABI: arguments are in RDI, RSI, RDX, RCX, R8, R9, top of stack; return
    // value in RAX (which matches SYSRET!)
    match Syscall::from_repr(syscall) {
        Some(Syscall::Read) => syscall_read(arg1 as i32, arg2 as *mut c_void, arg3),
        Some(Syscall::Write) => syscall_write(arg1 as i32, arg2 as *const c_void, arg3),
        Some(Syscall::Exit) => syscall_exit(arg1 as i32),
        Some(Syscall::Mmap) => {
            syscall_mmap(arg1 as *const c_void, arg2, arg3, arg4, arg5 as i32, arg6)
        }
        Some(Syscall::Fsync) => syscall_fsync(arg1 as i32),
        Some(Syscall::UnstableSwitchProcess) => {
            syscall_unstable_switch_proccess(arg1 as *mut c_void, arg2)
        }
        None => Errno::ENOSYS as isize,
    }
}

/// Main entry point for system calls in the Oak Restricted Kernel.
///
/// As we only support x86-64, we rely on the `SYSCALL`/`SYSRET` mechanism to
/// invoke system calls.
///
/// The system calls follow the Linux calling convention:
/// <https://github.com/torvalds/linux/blob/master/arch/x86/entry/calling.h>
///
/// In short:
///   - system call number is in `RAX`
///   - arguments go in `RDI`, `RSI`, `RDX`, `RCX`, `R8`, `R9`
///   - return value is in `RAX`
///
/// For the list of system calls that are supported, see the
/// `oak_restricted_kernel_interface` crate.
#[naked]
extern "C" fn syscall_entrypoint() {
    // When user code uses `SYSCALL`, the following happens (abridged):
    //  - RIP of the instruction following the SYSCALL will be in RCX
    //  - RFLAGS will be saved in R11
    //  - new RIP will be loaded from LSTAR (see `enable_syscalls()`)
    //  - CS and SS selectors will be loaded from STAR (see `init_gdt()` in
    //    `descriptors.rs`)
    //  - CPL will be forced to zero.
    //
    // For `SYSRET`, the fast system return:
    //  - lower 32 bits of RFLAGS will be loaded from R11, upper 32 are cleared
    //  - RIP will be loaded from RCX
    //  - CS and SS selectors will be loaded from STAR (see `init_gdt()` in
    //    `descriptors.rs`)
    //  - CPL will be forced to 3
    //
    // Note that (a) this does not preserve RCX and R11, which the user code will
    // take into account, and (b) SYSRET will always go back to ring 3.
    //
    // See SYSCALL and SYSRET in AMD64 Architecture Programmer's Manual, Volume 3
    // for more details.
    unsafe {
        asm! {
            // Switch to the syscall stack
            "swapgs", // switch to kernel GS
            "mov gs:[0x8], rsp", // save user RSP
            "mov gs:[0x10], rcx", // save user RIP
            "mov gs:[0x18], r11", // save user RFLAGS
            "mov rsp, gs:[0x0]", // switch to kernel stack

            // Save mutable registers other than RAX, RCX and R11 (the first is trashed for the return value;
            // the latter two are are stored in gsdata).
            "push rsi",
            "push rdi",
            "push rdx",
            "push rbx",
            "push r8",
            "push r9",
            "push r10",

            // Make sure the stack is 16-byte aligned.
            "sub rsp, 8",

            // Back up the AVX registers.
            // TODO(#3329): Update interrupt handler macro to support AVX, SSE or neither.
            "sub rsp, 16*32",
            "vmovups [rsp + 0*32], YMM0",
            "vmovups [rsp + 1*32], YMM1",
            "vmovups [rsp + 2*32], YMM2",
            "vmovups [rsp + 3*32], YMM3",
            "vmovups [rsp + 4*32], YMM4",
            "vmovups [rsp + 5*32], YMM5",
            "vmovups [rsp + 6*32], YMM6",
            "vmovups [rsp + 7*32], YMM7",
            "vmovups [rsp + 8*32], YMM8",
            "vmovups [rsp + 9*32], YMM9",
            "vmovups [rsp + 10*32], YMM10",
            "vmovups [rsp + 11*32], YMM11",
            "vmovups [rsp + 12*32], YMM12",
            "vmovups [rsp + 13*32], YMM13",
            "vmovups [rsp + 14*32], YMM14",
            "vmovups [rsp + 15*32], YMM15",

            // Shuffle around register values to match sysv calling convention, and escape into
            // proper Rust code from the assembly.
            "sub rsp, 8",
            "push r9",
            "mov r9, r8",
            "mov r8, r10",
            "mov rcx, rdx",
            "mov rdx, rsi",
            "mov rsi, rdi",
            "mov rdi, rax",
            "call {HANDLER}",
            "pop r9",
            "add rsp, 8",

            // Restore AVX registers.
            "vmovups YMM0, [rsp + 0*32]",
            "vmovups YMM1, [rsp + 1*32]",
            "vmovups YMM2, [rsp + 2*32]",
            "vmovups YMM3, [rsp + 3*32]",
            "vmovups YMM4, [rsp + 4*32]",
            "vmovups YMM5, [rsp + 5*32]",
            "vmovups YMM6, [rsp + 6*32]",
            "vmovups YMM7, [rsp + 7*32]",
            "vmovups YMM8, [rsp + 8*32]",
            "vmovups YMM9, [rsp + 9*32]",
            "vmovups YMM10, [rsp + 10*32]",
            "vmovups YMM11, [rsp + 11*32]",
            "vmovups YMM12, [rsp + 12*32]",
            "vmovups YMM13, [rsp + 13*32]",
            "vmovups YMM14, [rsp + 14*32]",
            "vmovups YMM15, [rsp + 15*32]",
            "add rsp, 16*32",

            // Undo stack alignment.
            "add rsp, 8",
            // Restore scratch registers.
            "pop r10",
            "pop r9",
            "pop r8",
            "pop rbx",
            "pop rdx",
            "pop rdi",
            "pop rsi",

            // Restore user values in preparation for SYSRET.
            // We don't save the kernel stack value; we'll just overwrite what's there next time
            // a syscall is invoked.
            "mov rsp, gs:[0x8]", // restore user RSP
            "mov rcx, gs:[0x10]", // restore user RIP
            "mov r11, gs:[0x18]", // restore user RFLAGS
            "swapgs", // restore user GS

            // Back to user code in Ring 3.
            "sysretq",
            HANDLER = sym syscall_handler,
            options(noreturn)
        }
    }
}
