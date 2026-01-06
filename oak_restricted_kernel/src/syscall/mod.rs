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
pub mod event_log;
mod fd;
mod key;
pub mod mmap;
mod process;
mod stdio;

mod create_process;
mod switch_process;

#[cfg(test)]
mod tests;

use alloc::{boxed::Box, vec::Vec};
use core::{arch::naked_asm, ffi::c_void, mem::offset_of, ptr::addr_of_mut};

use oak_channel::Channel;
use oak_restricted_kernel_interface::{Errno, Syscall};
use x86_64::{
    registers::{
        control::Efer,
        model_specific::{EferFlags, GsBase, KernelGsBase, LStar},
    },
    structures::paging::PhysFrame,
    PhysAddr, VirtAddr,
};

use self::{
    create_process::syscall_unstable_create_proccess,
    fd::{syscall_fsync, syscall_read, syscall_write},
    mmap::syscall_mmap,
    process::syscall_exit,
    switch_process::syscall_unstable_switch_proccess,
};
use crate::mm;

pub fn enable_syscalls(
    channel: Box<dyn Channel>,
    dice_data: dice_data::DiceData,
    encoded_event_log: Vec<u8>,
) {
    channel::register(channel);
    stdio::register();
    key::register();
    dice_data::register(dice_data);
    event_log::register(encoded_event_log);

    GsData::setup();

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
        Some(Syscall::UnstableCreateProcess) => {
            syscall_unstable_create_proccess(arg1 as *mut c_void, arg2)
        }
        Some(Syscall::UnstableSwitchProcess) => syscall_unstable_switch_proccess(arg1),
        None => Errno::ENOSYS as isize,
    }
}

const MAX_PROCESSES: usize = 16;

static mut GS_DATA: GsData = GsData {
    kernel_sp: VirtAddr::zero(),
    user_stack_pointers: [VirtAddr::zero(); MAX_PROCESSES],
    current_pid: 0,
    // Safety: placeholders that will be overwritten before use.
    user_pml4s: [unsafe { PhysFrame::from_start_address_unchecked(PhysAddr::zero()) };
        MAX_PROCESSES],
};

/// State we need to track for system calls.
#[repr(C, align(16))]
#[derive(Debug)]
pub(crate) struct GsData {
    /// Kernel stack pointer (what to set in RSP after saving user RSP).
    kernel_sp: VirtAddr,

    /// Current process ID.
    current_pid: usize,

    /// Array of user stack pointers (RSP) for each process, by PID.
    user_stack_pointers: [VirtAddr; MAX_PROCESSES],

    /// Array of root page tables for each process, by PID.
    user_pml4s: [PhysFrame; MAX_PROCESSES],
}

impl GsData {
    pub fn setup() {
        // Allocate a stack for the system call handler.
        let kernel_sp = mm::allocate_stack();

        // Store the gsdata structure in the kernel heap.
        // We need the GsData to stick around statically, so we'll leak it here.
        //
        // Safety: This is called during initialization, so we know no other threads are
        // accessing GS_DATA
        unsafe {
            GS_DATA.kernel_sp = kernel_sp;
            KernelGsBase::write(VirtAddr::from_ptr(addr_of_mut!(GS_DATA)));
            GsBase::write(VirtAddr::from_ptr(addr_of_mut!(GS_DATA)));
        };
    }

    /// Registers a process and returns its pid.
    ///
    /// Safety: this function must only be called once syscalls have been setup.
    pub unsafe fn register_process(process_pml4: PhysFrame) -> anyhow::Result<usize> {
        #[allow(static_mut_refs)]
        let free_pid = GS_DATA.user_pml4s.iter().position(|&frame| frame.start_address().is_null());
        match free_pid {
            None => Err(anyhow::Error::msg(
                "all slots for processes are occupied, no more processes can be registered",
            )),
            Some(pid) => {
                GS_DATA.user_pml4s[pid] = process_pml4;
                Ok(pid)
            }
        }
    }

    /// Get the current process ID from the GsData instance in the GS register.
    ///
    /// Safety: this function must only be called once syscalls have been setup.
    pub unsafe fn get_current_pid() -> usize {
        GS_DATA.current_pid
    }

    /// Set the current process ID in the GsData instance in the GS register and
    /// loads its pml4.
    ///
    /// Safety: this function must only be called once syscalls have been setup.
    /// Changes the root page table, so addresses in userspace will be invalid.
    /// Caller must ensure those side effects are okay.
    pub unsafe fn set_current_pid(pid: usize) -> Result<(), anyhow::Error> {
        #[allow(static_mut_refs)]
        GS_DATA
            .user_pml4s
            .get(pid)
            .ok_or(anyhow::Error::msg("Invalid PID: out of range"))?
            .start_address()
            .is_null()
            .then(|| {
                Err::<(), anyhow::Error>(anyhow::Error::msg("Invalid PID: not an active process"))
            })
            .transpose()?;
        // Safety: the new page table maintains the same mappings for kernel space.
        crate::PAGE_TABLES.lock().replace(GS_DATA.user_pml4s[pid]);
        GS_DATA.current_pid = pid;
        Ok(())
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
        naked_asm! {
            // Switch to kernel GS.
            "swapgs",

            // Save user general-purpose registers to user stack.
            // rax is not saved as it holds the syscall identifier.
            "push rbx",
            "push rcx",
            "push rdx",
            "push rsi",
            "push rdi",
            "push rbp",
            "push r8",
            "push r9",
            "push r10",
            "push r11", // the syscall instruction saved user RFLAGS into r11
            "push r12",
            "push r13",
            "push r14",
            "push r15",

            // Save user AVX registers to user stack.
            // AVX registers (e.g., ymm0) are not saved using 'push' because they are 256 bits wide
            // (or 512 bits in AVX-512) and 'push' is designed for pushing 16-bit, 32-bit, or 64-bit values.
            // Additionally, AVX instructions often prefer 32-byte aligned memory access, which may not
            // be guaranteed when using 'push' to place values on the stack.
            "sub rsp, 512",
            "vmovups [rsp + 0*32], ymm0",
            "vmovups [rsp + 1*32], ymm1",
            "vmovups [rsp + 2*32], ymm2",
            "vmovups [rsp + 3*32], ymm3",
            "vmovups [rsp + 4*32], ymm4",
            "vmovups [rsp + 5*32], ymm5",
            "vmovups [rsp + 6*32], ymm6",
            "vmovups [rsp + 7*32], ymm7",
            "vmovups [rsp + 8*32], ymm8",
            "vmovups [rsp + 9*32], ymm9",
            "vmovups [rsp + 10*32], ymm10",
            "vmovups [rsp + 11*32], ymm11",
            "vmovups [rsp + 12*32], ymm12",
            "vmovups [rsp + 13*32], ymm13",
            "vmovups [rsp + 14*32], ymm14",
            "vmovups [rsp + 15*32], ymm15",

            // Save user stack pointer to GsData.
            "mov r15, gs:[{OFFSET_CURRENT_PID}]",
            "shl r15, {POINTER_SIZE_SHIFT}", // Multiply by size of VirtAddr
            "add r15, {OFFSET_USER_STACK_POINTERS}",
            "mov gs:[r15], rsp",

             // Switch to kernel stack.
            "mov rsp, gs:[{OFFSET_KERNEL_STACK_POINTER}]",

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

            // Re-calculate offset of the user stack pointer, the current pid may have changed.
            "mov r15, gs:[{OFFSET_CURRENT_PID}]",
            "shl r15, {POINTER_SIZE_SHIFT}", // Multiply by size of VirtAddr
            "add r15, {OFFSET_USER_STACK_POINTERS}",

            // Restore user stack pointer from GsData.
            "mov rsp, gs:[r15]",

            // Restore user AVX registers from user stack.
            "vmovups ymm15, [rsp + 15*32]",
            "vmovups ymm14, [rsp + 14*32]",
            "vmovups ymm13, [rsp + 13*32]",
            "vmovups ymm12, [rsp + 12*32]",
            "vmovups ymm11, [rsp + 11*32]",
            "vmovups ymm10, [rsp + 10*32]",
            "vmovups ymm9, [rsp + 9*32]",
            "vmovups ymm8, [rsp + 8*32]",
            "vmovups ymm7, [rsp + 7*32]",
            "vmovups ymm6, [rsp + 6*32]",
            "vmovups ymm5, [rsp + 5*32]",
            "vmovups ymm4, [rsp + 4*32]",
            "vmovups ymm3, [rsp + 3*32]",
            "vmovups ymm2, [rsp + 2*32]",
            "vmovups ymm1, [rsp + 1*32]",
            "vmovups ymm0, [rsp + 0*32]",
            "add rsp, 512",

            // Restore user general-purpose registers from user stack.
            "pop r15",
            "pop r14",
            "pop r13",
            "pop r12",
            "pop r11", // the sysret instruction will copy r11 into RFLAGS
            "pop r10",
            "pop r9",
            "pop r8",
            "pop rbp",
            "pop rdi",
            "pop rsi",
            "pop rdx",
            "pop rcx",
            "pop rbx",
            // rax is not restored as it holds the syscall return value.

            // Restore user GS.
            "swapgs",

            // Back to user code in Ring 3.
            "sysretq",
            HANDLER = sym syscall_handler,
            OFFSET_KERNEL_STACK_POINTER = const(offset_of!(GsData, kernel_sp)),
            OFFSET_USER_STACK_POINTERS = const(offset_of!(GsData, user_stack_pointers)),
            OFFSET_CURRENT_PID = const(offset_of!(GsData, current_pid)),
            POINTER_SIZE_SHIFT = const(core::mem::size_of::<VirtAddr>().trailing_zeros()),
        }
    }
}
