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

use crate::i8042;
use core::ops::Deref;
use lazy_static::lazy_static;
use log::error;
use x86_64::structures::idt::{InterruptDescriptorTable, InterruptStackFrame};

lazy_static! {
    static ref IDT: InterruptDescriptorTable = {
        let mut idt = InterruptDescriptorTable::new();
        idt.double_fault.set_handler_fn(double_fault_handler);
        idt
    };
}

extern "x86-interrupt" fn double_fault_handler(
    stack_frame: InterruptStackFrame,
    _error_code: u64,
) -> ! {
    // We're not calling `panic!` here because (a) the panic location would be all wrong (the error
    // is not in the fault handler itself as the location would suggest), (b) in theory the
    // panic handler itself could cause a double fault, and (c) we want to be sure that we shut
    // down the machine after us.
    // Note that for double fault handlers the error code will always be 0, so there's no point in
    // logging that.
    error!("KERNEL PANIC: DOUBLE FAULT");
    error!(
        "Instruction pointer: {:#016x}",
        stack_frame.deref().instruction_pointer.as_u64()
    );
    error!("Code segment: {:#x}", stack_frame.deref().code_segment);
    error!(
        "Stack pointer: {:#016x}",
        stack_frame.deref().stack_pointer.as_u64()
    );
    error!("Stack segment: {:#x}", stack_frame.deref().stack_segment);
    error!("CPU flags: {:#x}", stack_frame.deref().cpu_flags);
    i8042::shutdown();
}

pub fn init_idt() {
    IDT.load();
}
