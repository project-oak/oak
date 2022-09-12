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

#![no_std]
#![no_main]

use core::{arch::asm, ffi::c_void, panic::PanicInfo};
use x86_64::{
    instructions::{hlt, interrupts::int3, segmentation::Segment},
    registers::{
        control::{Cr3, Cr3Flags},
        segmentation::*,
    },
    structures::{
        gdt::{Descriptor, GlobalDescriptorTable, SegmentSelector},
        idt::InterruptDescriptorTable,
        paging::{
            page::Size2MiB,
            page_table::{PageTable, PageTableFlags},
            PageSize, PhysFrame,
        },
    },
    PhysAddr, VirtAddr,
};
mod asm;

// Magic constants where various data structures will be stored.
// Many of these are set to be same as with crosvm; see
// https://google.github.io/crosvm/appendix/memory_layout.html for more details.
const BOOT_GDT_ADDR: PhysAddr = PhysAddr::new(0x1500);
// The GDT provided by crosvm has 4 entries, which means that the IDT can go immediately after that
// to address 0x1520. The Rust x86_64::GlobalDescriptorTable has 8 entries instead of 4; therefore,
// we must move our IDT data structure a bit lower in memory.
const BOOT_IDT_ADDR: PhysAddr = PhysAddr::new(0x1550);
const BOOT_PML4_ADDR: PhysAddr = PhysAddr::new(0x9000);
const BOOT_PDPT_ADDR: PhysAddr = PhysAddr::new(0xA000);
const BOOT_PD_ADDR: PhysAddr = PhysAddr::new(0xB000);

extern "C" {
    #[link_name = "pd_offset"]
    static BIOS_PD: c_void;
}

/// Creates page tables that identity-map the first 1GiB of memory using 2MiB hugepages.
pub fn create_page_tables(pml4: &mut PageTable, pdpt: &mut PageTable, pd: &mut PageTable) {
    pml4.zero();
    pml4[0].set_addr(
        PhysAddr::new(pdpt as *const _ as u64),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );

    pdpt.zero();
    pdpt[0].set_addr(
        PhysAddr::new(pd as *const _ as u64),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );

    pd.iter_mut().enumerate().for_each(|(i, entry)| {
        entry.set_addr(
            PhysAddr::new((i as u64) * Size2MiB::SIZE),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::HUGE_PAGE,
        );
    });
}

pub fn create_gdt(gdt: &mut GlobalDescriptorTable) -> (SegmentSelector, SegmentSelector) {
    *gdt = GlobalDescriptorTable::new();
    let cs = gdt.add_entry(Descriptor::kernel_code_segment());
    let ds = gdt.add_entry(Descriptor::kernel_data_segment());
    (cs, ds)
}

pub fn create_idt(idt: &mut InterruptDescriptorTable) {
    *idt = InterruptDescriptorTable::new();
}

/// Passes control to the operating system kernel. No more code from the BIOS will run.
///
/// # Safety
///
/// This assumes that the kernel entry point is valid.
pub unsafe fn jump_to_kernel(entry_point: VirtAddr) -> ! {
    asm!(
        // Boot stack pointer
        "mov $0x8000, %rsp",
        // Zero page address
        "mov $0x7000, %rsi",
        // ...and away we go!
        "jmp *{0}",
        in(reg) entry_point.as_u64(),
        options(noreturn, att_syntax)
    );
}

#[no_mangle]
pub extern "C" fn rust64_start() -> ! {
    /* Set up the machine according to the 64-bit Linux boot protocol.
     * See https://www.kernel.org/doc/html/latest/x86/boot.html#id1 for the particular requirements.
     */

    // Safety, for all these data structure dereferences: The addresses are to well-known locations,
    // same as crosvm is using, in the lowest 1MB of memory which we know is valid.
    let gdt = unsafe { &mut *(BOOT_GDT_ADDR.as_u64() as *mut GlobalDescriptorTable) };
    let (cs, ds) = create_gdt(gdt);
    gdt.load();
    // Safety: we've set up the valid data structures in create_gdt, above.
    unsafe {
        CS::set_reg(cs);
        DS::set_reg(ds);
        ES::set_reg(ds);
        FS::set_reg(ds);
        GS::set_reg(ds);
        SS::set_reg(ds);
    }

    let idt = unsafe { &mut *(BOOT_IDT_ADDR.as_u64() as *mut InterruptDescriptorTable) };
    create_idt(idt);
    idt.load();

    let pml4 = unsafe { &mut *(BOOT_PML4_ADDR.as_u64() as *mut PageTable) };
    let pdpt = unsafe { &mut *(BOOT_PDPT_ADDR.as_u64() as *mut PageTable) };
    let pd = unsafe { &mut *(BOOT_PD_ADDR.as_u64() as *mut PageTable) };
    create_page_tables(pml4, pdpt, pd);
    /* We need to do some trickery here. All of the stage0 code is somewhere within [4G-2M; 4G).
     * Thus, let's keep our own last PD, so that we can continue executing after reloading the
     * page tables.
     */
    // Safety: dereferencing the raw pointer is safe as that's the currently in-use page directory.
    pdpt[3].set_addr(
        PhysAddr::new((unsafe { &BIOS_PD as *const _ }) as u64),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );
    // Safety: changing the page tables here is safe because (a) we've populated the new page tables
    // at the well-known address of BOOT_PML4_ADDR and (b) we've ensured we keep the mapping for our
    // own code.
    unsafe {
        Cr3::write(
            PhysFrame::from_start_address(BOOT_PML4_ADDR).unwrap(),
            Cr3Flags::empty(),
        );
    }
    /* TODO(#3198): interrogate qemu for memory areas and set up the zero page. */

    /* TODO(#3199): determine the correct entry point from the ELF header */
    // Safety: this assumes the kernel is loaded at the given address.
    unsafe {
        jump_to_kernel(VirtAddr::new(0x200000));
    }
}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    // Trigger a breakpoint exception. As we don't have a #BP handler, this will triple fault and
    // terminate the program.
    int3();

    loop {
        hlt();
    }
}
