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

use core::{arch::naked_asm, ops::Deref};

use log::error;
use oak_sev_guest::{
    interrupts::{MutableInterruptStackFrame, mutable_interrupt_handler_with_error_code},
    io::{IoPortFactory, PortFactoryWrapper, PortWrapper, PortWriter},
    msr::{SevStatus, get_cpuid_for_vc_exception},
};
use spinning_top::Spinlock;
use x86_64::{
    VirtAddr,
    registers::{control::Cr2, mxcsr::read},
    structures::idt::{InterruptDescriptorTable, InterruptStackFrame, PageFaultErrorCode},
};

use crate::{shutdown, snp::CPUID_PAGE};

static IDT: Spinlock<InterruptDescriptorTable> = Spinlock::new(InterruptDescriptorTable::new());

#[naked]
extern "x86-interrupt" fn general_protection_fault_handler(_: InterruptStackFrame, _: u64) {
    unsafe {
        naked_asm! {
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
            options(att_syntax)
        }
    }
}

extern "x86-interrupt" fn general_protection_fault_handler_inner(
    stack_frame: InterruptStackFrame,
    error_code: u64,
) {
    error!("KERNEL PANIC: GENERAL PROTECTION FAULT!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    error!("Error code: {:?}", error_code);
    shutdown::shutdown();
}

extern "x86-interrupt" fn breakpoint_handler(stack_frame: InterruptStackFrame) {
    log::error!("EXCEPTION: BREAKPOINT\n{:#?}", stack_frame);
}

extern "x86-interrupt" fn page_fault_handler(
    stack_frame: InterruptStackFrame,
    error_code: PageFaultErrorCode,
) {
    error!("KERNEL PANIC: PAGE FAULT");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    error!("Faulting virtual address: {:#018x}", Cr2::read_raw());
    error!("Error code: {:?}", error_code);
    shutdown::shutdown();
}

extern "x86-interrupt" fn double_fault_handler(
    stack_frame: InterruptStackFrame,
    _error_code: u64,
) -> ! {
    // We're not calling `panic!` here because (a) the panic location would be all
    // wrong (the error is not in the fault handler itself as the location would
    // suggest), (b) in theory the panic handler itself could cause a double
    // fault, and (c) we want to be sure that we shut down the machine after us.
    // Note that for double fault handlers the error code will always be 0, so
    // there's no point in logging that.
    error!("KERNEL PANIC: DOUBLE FAULT");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    error!("Code segment: {:#x}", stack_frame.deref().code_segment.0);
    error!("Stack pointer: {:#016x}", stack_frame.deref().stack_pointer.as_u64());
    error!("Stack segment: {:#x}", stack_frame.deref().stack_segment.0);
    error!("CPU flags: {:#x}", stack_frame.deref().cpu_flags);
    shutdown::shutdown();
}

mutable_interrupt_handler_with_error_code!(
    unsafe fn vmm_communication_exception_handler(
        stack_frame: &mut MutableInterruptStackFrame,
        error_code: u64,
    ) {
        match error_code {
            0x72 => {
                // Make sure it was triggered from a CPUID instruction.
                const CPUID_INSTRUCTION: u16 = 0xa20f;
                // Safety: we are copying two bytes and interpreting it as a
                // 16-bit number without making any other assumptions about
                // the layout.
                let instruction: u16 =
                    unsafe { core::ptr::read_unaligned(stack_frame.rip.as_ptr()) };
                if instruction != CPUID_INSTRUCTION {
                    panic!("INSTRUCTION WAS NOT CPUID");
                }

                if let Some(cpuid_page) = CPUID_PAGE.get() {
                    let target = stack_frame.into();
                    let count = cpuid_page.count as usize;
                    if let Some(found) =
                        cpuid_page.cpuid_data[0..count].iter().find(|item| item.input == target)
                    {
                        stack_frame.rax = found.output.eax as u64;
                        stack_frame.rbx = found.output.ebx as u64;
                        stack_frame.rcx = found.output.ecx as u64;
                        stack_frame.rdx = found.output.edx as u64;
                    } else {
                        // For now we just log the error so that we can see when this happens.
                        // TODO(#3470): Improve handling of incorrect/missing CPUID requests.
                        error!("KERNEL PANIC: REQUESTED CPUID NOT PRESENT IN CPUID PAGE");
                        error!("Instruction pointer: {:#016x}", stack_frame.rip.as_u64());
                        error!("RAX: {:#016x}", stack_frame.rax);
                        error!("RCX: {:#016x}", stack_frame.rcx);
                        shutdown::shutdown();
                    }
                } else {
                    let leaf = stack_frame.rax as u32;
                    // The MSR protocol does not support sub-leaf requests or leaf 0x0000_000D.
                    // See section 2.3.1 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf>
                    // TODO(#3470): Improve handling of incorrect/missing CPUID requests.
                    if stack_frame.rcx != 0 || leaf == 0x0000_000D {
                        error!("KERNEL PANIC: CPUID SUB-LEAF OR INVALID LEAD REQUESTED");
                        error!("Instruction pointer: {:#016x}", stack_frame.rip.as_u64());
                        error!("RAX: {:#016x}", stack_frame.rax);
                        error!("RCX: {:#016x}", stack_frame.rcx);
                        shutdown::shutdown();
                    }
                    get_cpuid_for_vc_exception(leaf, stack_frame).expect("error reading CPUID");
                }
                // CPUID instruction is 2 bytes long, so we advance the instruction pointer by
                // 2.
                stack_frame.rip += 2u64;
            }
            _ => {
                error!("KERNEL PANIC: UNHANDLED #VC EXCEPTION");
                error!("Instruction pointer: {:#016x}", stack_frame.rip.as_u64());
                error!("Error code: {:#x}", error_code);
                shutdown::shutdown();
            }
        }
    }
);

extern "x86-interrupt" fn divide_error_handler(stack_frame: InterruptStackFrame) {
    error!("KERNEL PANIC: DIVIDE BY ZERO!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    shutdown::shutdown();
}

extern "x86-interrupt" fn nmi_handler(stack_frame: InterruptStackFrame) {
    error!("KERNEL PANIC: NON-MASKABLE INTERRUPT!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    shutdown::shutdown();
}

extern "x86-interrupt" fn overflow_handler(stack_frame: InterruptStackFrame) {
    error!("KERNEL PANIC: OVERFLOW!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    shutdown::shutdown();
}

extern "x86-interrupt" fn bound_range_handler(stack_frame: InterruptStackFrame) {
    error!("KERNEL PANIC: BOUND RANGE EXCEEDED!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    shutdown::shutdown();
}

extern "x86-interrupt" fn invalid_opcode_handler(stack_frame: InterruptStackFrame) {
    error!("KERNEL PANIC: INVALID OPCODE!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    shutdown::shutdown();
}

extern "x86-interrupt" fn device_not_available_handler(stack_frame: InterruptStackFrame) {
    error!("KERNEL PANIC: DEVICE NOT AVAILABLE!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    shutdown::shutdown();
}

extern "x86-interrupt" fn invalid_tss_handler(stack_frame: InterruptStackFrame, error_code: u64) {
    error!("KERNEL PANIC: INVALID TSS!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    error!("Error code: {:?}", error_code);
    shutdown::shutdown();
}

extern "x86-interrupt" fn segment_not_present_handler(
    stack_frame: InterruptStackFrame,
    error_code: u64,
) {
    error!("KERNEL PANIC: SEGMENT NOT PRESENT!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    error!("Error code: {:?}", error_code);
    shutdown::shutdown();
}

extern "x86-interrupt" fn stack_exception_handler(
    stack_frame: InterruptStackFrame,
    error_code: u64,
) {
    error!("KERNEL PANIC: STACK EXCEPTION!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    error!("Error code: {:?}", error_code);
    shutdown::shutdown();
}

extern "x86-interrupt" fn x87_floating_point_handler(stack_frame: InterruptStackFrame) {
    error!("KERNEL PANIC: X87 FLOATING POINT EXCEPTION!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    shutdown::shutdown();
}

extern "x86-interrupt" fn alignment_check_handler(
    stack_frame: InterruptStackFrame,
    error_code: u64,
) {
    error!("KERNEL PANIC: ALIGNMENT CHECK EXCEPTION!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    error!("Error code: {:?}", error_code);
    shutdown::shutdown();
}

extern "x86-interrupt" fn machine_check_handler(stack_frame: InterruptStackFrame) -> ! {
    error!("KERNEL PANIC: MACHINE CHECK EXCEPTION!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    shutdown::shutdown();
}

extern "x86-interrupt" fn simd_fp_handler(stack_frame: InterruptStackFrame) {
    error!("KERNEL PANIC: SIMD FLOATING POINT EXCEPTION!");
    error!("Instruction pointer: {:#016x}", stack_frame.deref().instruction_pointer.as_u64());
    let mxcsr = read();
    error!("MXCSR: {:?}", mxcsr);

    shutdown::shutdown();
}

pub fn init_idt_early() {
    // The full list if interrupts is processor-specific.
    // For AMD, see Section 8.2 of the AMD64 Architecture Programmer's Manual,
    // Volume 2 for more details.
    let mut idt = IDT.lock();
    idt.divide_error.set_handler_fn(divide_error_handler); // vector 0

    // skipping vector 1 (debug)

    idt.non_maskable_interrupt.set_handler_fn(nmi_handler); // vector 2
    idt.breakpoint.set_handler_fn(breakpoint_handler); // vector 3
    idt.overflow.set_handler_fn(overflow_handler); // vector 4
    idt.bound_range_exceeded.set_handler_fn(bound_range_handler); // vector 5
    idt.invalid_opcode.set_handler_fn(invalid_opcode_handler); // vector 6
    idt.device_not_available.set_handler_fn(device_not_available_handler); // vector 7
    idt.double_fault.set_handler_fn(double_fault_handler); // vector 8

    // vector 9 is reserved

    idt.invalid_tss.set_handler_fn(invalid_tss_handler); // vector 10
    idt.segment_not_present.set_handler_fn(segment_not_present_handler); // vector 11
    idt.stack_segment_fault.set_handler_fn(stack_exception_handler); // vector 12
    idt.general_protection_fault.set_handler_fn(general_protection_fault_handler); // vector 13
    idt.page_fault.set_handler_fn(page_fault_handler); // vector 14

    // there is no vector 15

    idt.x87_floating_point.set_handler_fn(x87_floating_point_handler); // vector 16
    idt.alignment_check.set_handler_fn(alignment_check_handler); // vector 17
    idt.machine_check.set_handler_fn(machine_check_handler); // vector 18
    idt.simd_floating_point.set_handler_fn(simd_fp_handler); // vector 19

    // there is no vector 20

    let vc_handler_address = VirtAddr::new(vmm_communication_exception_handler as usize as u64);
    // Safety: we are passing a valid address of a function with the correct
    // signature.
    unsafe {
        idt.vmm_communication_exception.set_handler_addr(vc_handler_address); // vector 29
    }

    // Safety: unfortunately we have to escape from the borrow checker here, as we
    // know the IDT is 'static but the `idt` variable (the mutex lock) is not
    // 'static, so calling `idt.load()` will not work.
    unsafe { idt.load_unsafe() };
}

/// Updates the IDT to point the double fault handler to a separate stack.
///
/// # Safety
///
/// The caller needs to guarantee that the stack index is valid.
pub unsafe fn init_idt(double_fault_stack_index: u16) {
    let mut idt = IDT.lock();
    let opts = idt.double_fault.set_handler_fn(double_fault_handler);
    unsafe {
        opts.set_stack_index(double_fault_stack_index);
        idt.load_unsafe();
    }
}

struct Pic {
    command: PortWrapper<u8>,
    data: PortWrapper<u8>,
}

impl Pic {
    pub fn new(factory: &PortFactoryWrapper, base: u16) -> Self {
        Self { command: factory.new_writer(base), data: factory.new_writer(base + 1) }
    }

    pub unsafe fn write_command(&mut self, command: u8) -> Result<(), &'static str> {
        unsafe { self.command.try_write(command) }
    }

    pub unsafe fn write_data(&mut self, data: u8) -> Result<(), &'static str> {
        unsafe { self.data.try_write(data) }
    }
}

/// Initializes the 8259 PIC and then immediately disables all exceptions.
///
/// # Safety
///
/// This uses raw I/O port access to talk to the PIC; the caller has to
/// guarantee there will not be any adverse effect if there's no PIC at those
/// ports.
pub unsafe fn init_pic8259(sev_status: SevStatus) -> Result<(), &'static str> {
    let io_port_factory = if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
        crate::ghcb::get_ghcb_port_factory()
    } else {
        PortFactoryWrapper::new_raw()
    };

    let mut pic0 = Pic::new(&io_port_factory, 0x20);
    let mut pic1 = Pic::new(&io_port_factory, 0xA0);

    // The initialization process is documented in https://wiki.osdev.org/8259_PIC
    // Tell the PICs we're going to start intializing them.
    unsafe {
        pic0.write_command(0x11)?; // ICW1_INIT | ICW1_ICW4
        pic1.write_command(0x11)?;

        // Byte 1: the interrupt offsets.
        pic0.write_data(0x20)?; // PIC0 interrupts start at vector 32
        pic1.write_data(0x28)?; // PIC1 interrupts start at vector 40

        // Byte 2: chanining between PICs.
        pic0.write_data(4)?; // PIC0: there's PIC1 at your IRQ 2
        pic1.write_data(2)?; // PIC1: your cascade identity

        // Byte 3: operation mode.
        pic0.write_data(0x01)?; // ICW4_8086
        pic1.write_data(0x01)?;

        // Finally, mask all interrupts as we're not going to use the PICs.
        pic0.write_data(0xFF)?;
        pic1.write_data(0xFF)?;
    }

    Ok(())
}
