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
mod read;

use alloc::boxed::Box;
use core::arch::asm;
use oak_channel::Channel;
use x86_64::{
    registers::{
        control::Efer,
        model_specific::{EferFlags, LStar},
    },
    VirtAddr,
};

pub fn enable_syscalls(channel: Box<dyn Channel>) {
    channel::init(channel);

    LStar::write(VirtAddr::new(syscall_entrypoint as *const fn() as u64));
    unsafe {
        Efer::update(|flags| flags.set(EferFlags::SYSTEM_CALL_EXTENSIONS, true));
    }
}

extern "sysv64" fn syscall_handler(syscall: usize) {}

// When user code uses `SYSCALL`, the following happens (abridged):
//  - RIP of the instruction following the SYSCALL will be in RCX
//  - RFLAGS will be saved in R11
//  - new RIP will be loaded from LSTAR (see `enable_syscalls()`)
//  - CS and SS selectors will be loaded from STAR (see `init_gdt()` in `descriptors.rs`)
//  - CPL will be forced to zero.
// All in all, it's like an interrupt, but with a different return method.
#[naked]
extern "C" fn syscall_entrypoint() {
    unsafe {
        asm! {
            "ud2",
            "call {HANDLER}",
            HANDLER = sym syscall_handler,
            options(att_syntax, noreturn)
        }
    }
}
