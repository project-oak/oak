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

use spinning_top::Spinlock;
use x86_64::{
    VirtAddr,
    instructions::tables::load_tss,
    registers::{model_specific::Star, segmentation::*},
    structures::{
        gdt::{Descriptor, GlobalDescriptorTable},
        tss::TaskStateSegment,
    },
};

struct Descriptors {
    gdt: GlobalDescriptorTable,
    tss: TaskStateSegment,
    kernel_cs_selector: SegmentSelector,
    kernel_ds_selector: SegmentSelector,
    user_cs_selector: SegmentSelector,
    user_ds_selector: SegmentSelector,
    tss_selector: SegmentSelector,
}

const DOUBLE_FAULT_STACK_INDEX: u16 = 1;

static DESCRIPTORS: Spinlock<Descriptors> = Spinlock::new(Descriptors {
    gdt: GlobalDescriptorTable::new(),
    tss: TaskStateSegment::new(),
    kernel_cs_selector: SegmentSelector::NULL,
    kernel_ds_selector: SegmentSelector::NULL,
    user_cs_selector: SegmentSelector::NULL,
    user_ds_selector: SegmentSelector::NULL,
    tss_selector: SegmentSelector::NULL,
});

/// Does basic initialization of the GDT for the kernel itself.
pub fn init_gdt_early() {
    let mut descriptors = DESCRIPTORS.lock();
    descriptors.kernel_cs_selector = descriptors.gdt.append(Descriptor::kernel_code_segment());
    descriptors.kernel_ds_selector = descriptors.gdt.append(Descriptor::kernel_data_segment());

    // Safety: descriptors are 'static, so this is safe to load, but unfortunately
    // the fact isn't visible through the MutexGuard.
    unsafe {
        descriptors.gdt.load_unsafe();
    }

    // Safety: it's safe to load these segments as we've initialized the GDT just
    // above.
    unsafe {
        CS::set_reg(descriptors.kernel_cs_selector);
        DS::set_reg(descriptors.kernel_ds_selector);
        ES::set_reg(descriptors.kernel_ds_selector);
        FS::set_reg(descriptors.kernel_ds_selector);
        GS::set_reg(descriptors.kernel_ds_selector);
        SS::set_reg(descriptors.kernel_ds_selector);
    }
}

/// Adds descriptors required for Ring 3 to the GDT.
pub fn init_gdt(double_fault_stack: VirtAddr, privileged_interrupt_stack: VirtAddr) -> u16 {
    let mut descriptors = DESCRIPTORS.lock();

    // If an interrupt triggers a switch to Ring 0, the CPU will switch to the
    // privileged stack.
    descriptors.tss.privilege_stack_table[0] = privileged_interrupt_stack;
    // If we double fault (which means something is _really_ wrong), the CPU will
    // switch to this stack.
    descriptors.tss.interrupt_stack_table[DOUBLE_FAULT_STACK_INDEX as usize] = double_fault_stack;

    descriptors.user_ds_selector = descriptors.gdt.append(Descriptor::user_data_segment());
    descriptors.user_cs_selector = descriptors.gdt.append(Descriptor::user_code_segment());
    // Safety: we know that descriptors are 'static as they are stored in the static
    // variable, but unfortunately that fact is not visible through the
    // MutexGuard. Thus, we need to rely on `transmute()` to extend the lifetime
    // and use `load_unsafe()` to actually load the GDT.
    let tss_descriptor = Descriptor::tss_segment(unsafe {
        core::mem::transmute::<
            &x86_64::structures::tss::TaskStateSegment,
            &x86_64::structures::tss::TaskStateSegment,
        >(&descriptors.tss)
    });
    descriptors.tss_selector = descriptors.gdt.append(tss_descriptor);
    unsafe {
        descriptors.gdt.load_unsafe();
        load_tss(descriptors.tss_selector);
    }

    // Set IA32_STAR MSR for syscalls.
    Star::write(
        descriptors.user_cs_selector,   // Code segment for SYSRET
        descriptors.user_ds_selector,   // Stack segment for SYSRET
        descriptors.kernel_cs_selector, // Code segment for SYSCALL
        descriptors.kernel_ds_selector, // Stack segment for SYSCALL
    )
    .expect("failed to set IA32_STAR MSR");

    DOUBLE_FAULT_STACK_INDEX
}
