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
use core::{arch::asm, ops::Deref};
use lazy_static::lazy_static;
use log::error;
use sev_guest::{
    interrupts::{mutable_interrupt_handler_with_error_code, MutableInterruptStackFrame},
    msr::get_cpuid_for_vc_exception,
};
use x86_64::{
    registers::control::Cr2,
    structures::idt::{InterruptDescriptorTable, InterruptStackFrame, PageFaultErrorCode},
    VirtAddr,
};

lazy_static! {
    static ref IDT: InterruptDescriptorTable = {
        let mut idt = InterruptDescriptorTable::new();
        idt.breakpoint.set_handler_fn(breakpoint_handler);                             // vector 3
        idt.double_fault.set_handler_fn(double_fault_handler);                         // vector 8
        idt.general_protection_fault.set_handler_fn(general_protection_fault_handler); // vector 13
        idt.page_fault.set_handler_fn(page_fault_handler);                             // vector 14

        let vc_handler_address =
            VirtAddr::new(vmm_communication_exception_handler as usize as u64);
        // Safety: we are passing a valid address of a function with the correct signature.
        unsafe {
            idt.vmm_communication_exception.set_handler_addr(vc_handler_address);      // vector 29
        }

        idt
    };
}

#[naked]
extern "x86-interrupt" fn general_protection_fault_handler(_: InterruptStackFrame, _: u64) {
    unsafe {
        asm! {
            "push %rax",            // save old rax value
            "mov 16(%rsp), %rax",   // rax = rsp + 16 (address of the return RIP)
            "cmpw $0x320F, (%rax)", // is RIP pointing to 0x320F (RDMSR)?
            "jne 2f",               // if not, jump to label 2
            "add $2, %rax",         // increment rax by 2 (size of RDMSR instruction)
            "add $24, %rsp",        // drop the saved RAX, error code, and Return IP
            "push %rax",            // put Return IP back on the stack for iretq
            "xor %rax, %rax",       // zero out RAX
            "xor %rdx, %rdx",       // zero out RDX
            "iretq",                // and go back claiming we've executed the RDMSR
            "2:",                   // it wasn't because of `rdmsr`
            "pop %rax",             // restore old rax value. We're now back at the initial state.
            "jmp {}",               // Let the Rust code take care of it. We jmp instead of call, as the
                                    // Rust function will call `iretq` instead of `ret` at the end.
            sym general_protection_fault_handler_inner,
            options(att_syntax, noreturn)
        }
    }
}

extern "x86-interrupt" fn general_protection_fault_handler_inner(
    stack_frame: InterruptStackFrame,
    error_code: u64,
) {
    error!("KERNEL PANIC: GENERAL PROTECTION FAULT!");
    error!(
        "Instruction pointer: {:#016x}",
        stack_frame.deref().instruction_pointer.as_u64()
    );
    error!("Error code: {:?}", error_code);
    i8042::shutdown();
}

extern "x86-interrupt" fn breakpoint_handler(stack_frame: InterruptStackFrame) {
    log::error!("EXCEPTION: BREAKPOINT\n{:#?}", stack_frame);
}

extern "x86-interrupt" fn page_fault_handler(
    stack_frame: InterruptStackFrame,
    error_code: PageFaultErrorCode,
) {
    error!("KERNEL PANIC: PAGE FAULT");
    error!(
        "Instruction pointer: {:#016x}",
        stack_frame.deref().instruction_pointer.as_u64()
    );
    error!("Faulting virtual address: {:#018x}", Cr2::read());
    error!("Error code: {:?}", error_code);
    i8042::shutdown();
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

mutable_interrupt_handler_with_error_code!(
    unsafe fn vmm_communication_exception_handler(
        stack_frame: &mut MutableInterruptStackFrame,
        error_code: u64,
    ) {
        match error_code {
            0x72 => {
                if stack_frame.rcx != 0 {
                    error!("KERNEL PANIC: CPUID SUB-LEAF REQUESTED");
                    error!("Instruction pointer: {:#016x}", stack_frame.rip.as_u64());
                    error!("RAX: {:#016x}", stack_frame.rax);
                    error!("RCX: {:#016x}", stack_frame.rcx);
                    i8042::shutdown();
                }
                let leaf = stack_frame.rax as u32;
                get_cpuid_for_vc_exception(leaf, stack_frame).expect("Error reading CPUID");
            }
            _ => {
                error!("KERNEL PANIC: UNHANDLED #VC EXCEPTION");
                error!("Instruction pointer: {:#016x}", stack_frame.rip.as_u64());
                error!("Error code: {:#x}", error_code);
                i8042::shutdown();
            }
        }
    }
);

pub fn init_idt() {
    IDT.load();
}
