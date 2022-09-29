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

use core::{
    arch::asm,
    ffi::c_void,
    mem::{size_of, zeroed, MaybeUninit},
    panic::PanicInfo,
};
use oak_linux_boot_params::BootParams;
use sev_guest::instructions::{pvalidate, InstructionError, PageSize as SevPageSize, Validation};
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
            frame::PhysFrameRange,
            page_table::{PageTable, PageTableFlags},
            PageSize, PhysFrame, Size2MiB, Size4KiB,
        },
    },
    PhysAddr, VirtAddr,
};
mod asm;

#[link_section = ".boot.gdt"]
static mut BOOT_GDT: MaybeUninit<GlobalDescriptorTable> = MaybeUninit::uninit();
#[link_section = ".boot.idt"]
static mut BOOT_IDT: MaybeUninit<InterruptDescriptorTable> = MaybeUninit::uninit();
#[link_section = ".boot.zero_page"]
static mut BOOT_ZERO_PAGE: MaybeUninit<BootParams> = MaybeUninit::uninit();
#[link_section = ".boot.pml4"]
static mut BOOT_PML4: MaybeUninit<PageTable> = MaybeUninit::uninit();
#[link_section = ".boot.pdpt"]
static mut BOOT_PDPT: MaybeUninit<PageTable> = MaybeUninit::uninit();
#[link_section = ".boot.pd"]
static mut BOOT_PD: MaybeUninit<PageTable> = MaybeUninit::uninit();
#[link_section = ".boot.unmeasured"]
#[used]
static mut SEV_UNMEASURED: MaybeUninit<[u8; 4096]> = MaybeUninit::uninit();
#[link_section = ".boot.secrets"]
static mut SEV_SECRETS: MaybeUninit<sev_guest::secrets::SecretsPage> = MaybeUninit::uninit();
#[link_section = ".boot.cpuid"]
static mut SEV_CPUID: MaybeUninit<sev_guest::cpuid::CpuidPage> = MaybeUninit::uninit();

#[link_section = ".boot"]
static mut CC_BLOB_SEV_INFO: MaybeUninit<oak_linux_boot_params::CCBlobSevInfo> =
    MaybeUninit::uninit();
#[link_section = ".boot"]
static mut CC_SETUP_DATA: MaybeUninit<oak_linux_boot_params::CCSetupData> = MaybeUninit::uninit();

extern "C" {
    #[link_name = "pd_addr"]
    static BIOS_PD: c_void;

    #[link_name = "boot_stack_pointer"]
    static BOOT_STACK_POINTER: c_void;

    #[link_name = "boot_data_structs_start"]
    static BOOT_DATA_STRUCTS_START: c_void;

    #[link_name = "boot_data_structs_end"]
    static BOOT_DATA_STRUCTS_END: c_void;
}

/// Creates page tables that identity-map the first 1GiB of memory using 2MiB hugepages.
pub fn create_page_tables(
    pml4: &mut PageTable,
    pdpt: &mut PageTable,
    pd: &mut PageTable,
    encrypted: u64,
) {
    pml4.zero();
    pml4[0].set_addr(
        PhysAddr::new(pdpt as *const _ as u64 | encrypted),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );

    pdpt.zero();
    pdpt[0].set_addr(
        PhysAddr::new(pd as *const _ as u64 | encrypted),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );

    pd.iter_mut().enumerate().for_each(|(i, entry)| {
        entry.set_addr(
            PhysAddr::new(((i as u64) * Size2MiB::SIZE) | encrypted),
            PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::HUGE_PAGE,
        );
    });
}

pub fn create_gdt(gdt: &mut GlobalDescriptorTable) -> (SegmentSelector, SegmentSelector) {
    let cs = gdt.add_entry(Descriptor::kernel_code_segment());
    let ds = gdt.add_entry(Descriptor::kernel_data_segment());
    (cs, ds)
}

pub fn create_idt(_idt: &mut InterruptDescriptorTable) {}

/// Passes control to the operating system kernel. No more code from the BIOS will run.
///
/// # Safety
///
/// This assumes that the kernel entry point is valid.
pub unsafe fn jump_to_kernel(entry_point: VirtAddr) -> ! {
    asm!(
        // Boot stack pointer
        "mov {1}, %rsp",
        // Zero page address
        "mov {2}, %rsi",
        // ...and away we go!
        "jmp *{0}",
        in(reg) entry_point.as_u64(),
        in(reg) &BOOT_STACK_POINTER as *const _ as u64,
        in(reg) BOOT_ZERO_PAGE.as_ptr() as u64,
        options(noreturn, att_syntax)
    );
}

/// Trait for abstracting the call to `PVALIDATE` over different page sizes and ranges.
trait Validator {
    fn pvalidate(self, validated: Validation) -> Result<(), InstructionError>;
}

impl Validator for PhysFrame<Size2MiB> {
    fn pvalidate(self, validated: Validation) -> Result<(), InstructionError> {
        match pvalidate(
            self.start_address().as_u64() as usize,
            SevPageSize::Page2MiB,
            validated,
        ) {
            // Safety: These unwraps are safe as this PhysFrame is aligned to 2 MiB, which is always
            // also aligned to 4 KiB.
            Err(InstructionError::FailSizeMismatch) => PhysFrame::<Size4KiB>::range(
                PhysFrame::from_start_address(self.start_address()).unwrap(),
                PhysFrame::from_start_address((self + 1).start_address()).unwrap(),
            )
            .pvalidate(validated),
            other => other,
        }
    }
}

impl Validator for PhysFrame<Size4KiB> {
    fn pvalidate(self, validated: Validation) -> Result<(), InstructionError> {
        pvalidate(
            self.start_address().as_u64() as usize,
            SevPageSize::Page4KiB,
            validated,
        )
    }
}

impl Validator for PhysFrameRange<Size4KiB> {
    fn pvalidate(self, validated: Validation) -> Result<(), InstructionError> {
        for frame in self {
            match frame.pvalidate(validated) {
                Err(InstructionError::ValidationStatusNotUpdated) => Ok(()),
                other => other,
            }?;
        }
        Ok(())
    }
}

impl Validator for PhysFrameRange<Size2MiB> {
    fn pvalidate(self, validated: Validation) -> Result<(), InstructionError> {
        for frame in self {
            match frame.pvalidate(validated) {
                Err(InstructionError::ValidationStatusNotUpdated) => Ok(()),
                other => other,
            }?;
        }
        Ok(())
    }
}

/// Entry point for the Rust code in the stage0 BIOS.
///
/// # Arguments
///
/// * `encrypted` - If not zero, the `encrypted`-th bit will be set in the page tables.
#[no_mangle]
pub extern "C" fn rust64_start(encrypted: u64) -> ! {
    let snp = if encrypted > 0 {
        // We're under some form of memory encryption, thus it's safe to access the SEV_STATUS MSR.
        sev_guest::msr::get_sev_status()
            .unwrap_or(sev_guest::msr::SevStatus::empty())
            .contains(sev_guest::msr::SevStatus::SNP_ACTIVE)
    } else {
        false
    };

    /* Set up the machine according to the 64-bit Linux boot protocol.
     * See https://www.kernel.org/doc/html/latest/x86/boot.html#id1 for the particular requirements.
     */

    // Before we access any memory, we need to ensure we've called `PVALIDATE` on the page.
    // Safety: as all of these are static mut-s, we need to wrap all access to them in `unsafe {}`.
    // This is safe, as (a) the linker script places them in memory in a way that's not overlapping,
    // and (b) we do not have threads in stage0 so we're not in danger of concurrent access.
    if snp {
        pvalidate(
            x86_64::addr::align_down(unsafe { BOOT_GDT.as_ptr() } as u64, 0x1000) as usize,
            SevPageSize::Page4KiB,
            Validation::Validated,
        )
        .unwrap();
    }
    let gdt = unsafe { BOOT_GDT.write(GlobalDescriptorTable::new()) };

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

    if snp {
        pvalidate(
            unsafe { BOOT_IDT.as_ptr() } as usize,
            SevPageSize::Page4KiB,
            Validation::Validated,
        )
        .unwrap();
    }
    let idt = unsafe { BOOT_IDT.write(InterruptDescriptorTable::new()) };

    create_idt(idt);
    idt.load();

    // We assume 0-th bit is never the encrypted bit.
    let encrypted = if encrypted > 0 { 1 << encrypted } else { 0 };

    if snp {
        pvalidate(
            unsafe { BOOT_PML4.as_ptr() } as usize,
            SevPageSize::Page4KiB,
            Validation::Validated,
        )
        .unwrap();
        pvalidate(
            unsafe { BOOT_PDPT.as_ptr() } as usize,
            SevPageSize::Page4KiB,
            Validation::Validated,
        )
        .unwrap();
        pvalidate(
            unsafe { BOOT_PD.as_ptr() } as usize,
            SevPageSize::Page4KiB,
            Validation::Validated,
        )
        .unwrap();
    }
    let pml4 = unsafe { BOOT_PML4.write(PageTable::new()) };
    let pdpt = unsafe { BOOT_PDPT.write(PageTable::new()) };
    let pd = unsafe { BOOT_PD.write(PageTable::new()) };
    create_page_tables(pml4, pdpt, pd, encrypted);
    /* We need to do some trickery here. All of the stage0 code is somewhere within [4G-2M; 4G).
     * Thus, let's keep our own last PD, so that we can continue executing after reloading the
     * page tables.
     */
    // Safety: dereferencing the raw pointer is safe as that's the currently in-use page directory.
    pdpt[3].set_addr(
        PhysAddr::new(unsafe { &BIOS_PD } as *const _ as u64 | encrypted),
        PageTableFlags::PRESENT | PageTableFlags::WRITABLE,
    );
    // Safety: changing the page tables here is safe because (a) we've populated the new page tables
    // at the well-known address of BOOT_PML4_ADDR and (b) we've ensured we keep the mapping for our
    // own code.
    unsafe {
        Cr3::write(
            PhysFrame::from_start_address(PhysAddr::new(BOOT_PML4.as_ptr() as u64)).unwrap(),
            Cr3Flags::empty(),
        );
    }
    /* TODO(#3198): interrogate qemu for memory areas and set up the zero page. */

    // Safety: We assume the VMM has filled in the basic zero page for us. This is not true with
    // qemu. In the future, construction of the full zero page should be in here, and instead of
    // `assume_init_mut` we will use the safe `write` to zero it out and get a mutable reference.
    let zero_page = unsafe { BOOT_ZERO_PAGE.assume_init_mut() };

    if snp {
        PhysFrame::<Size4KiB>::range(
            PhysFrame::from_start_address(PhysAddr::new(
                unsafe { &BOOT_DATA_STRUCTS_START } as *const _ as u64
            ))
            .unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(
                unsafe { &BOOT_DATA_STRUCTS_END } as *const _ as u64
            ))
            .unwrap(),
        )
        .pvalidate(Validation::Validated)
        .unwrap();

        let setup_data = unsafe { CC_SETUP_DATA.write(zeroed()) };
        let cc_blob = unsafe { CC_BLOB_SEV_INFO.write(zeroed()) };

        setup_data.header.type_ = oak_linux_boot_params::SetupDataType::CCBlob;
        setup_data.header.len = (size_of::<oak_linux_boot_params::CCSetupData>()
            - size_of::<oak_linux_boot_params::SetupData>()) as u32;
        setup_data.cc_blob_address = cc_blob as *const _ as u32;

        cc_blob.magic = oak_linux_boot_params::CC_BLOB_SEV_INFO_MAGIC;
        cc_blob.version = 1;
        cc_blob.secrets_phys = unsafe { SEV_SECRETS.as_ptr() } as usize;
        cc_blob.secrets_len = size_of::<sev_guest::secrets::SecretsPage>() as u32;
        cc_blob.cpuid_phys = unsafe { SEV_CPUID.as_ptr() } as usize;
        cc_blob.cpuid_len = size_of::<sev_guest::cpuid::CpuidPage>() as u32;

        // Put our header as the first element in the linked list.
        setup_data.header.next = zero_page.hdr.setup_data;
        zero_page.hdr.setup_data = &setup_data.header as *const oak_linux_boot_params::SetupData;
    }

    // Temporary hack: PVALIDATE [2..32] MiB of physical memory, ignoring any failures to update
    // the status for now. In the future, after we have determined the physical memory
    // layout, we should call PVALIDATE on all of it.
    if snp {
        PhysFrame::<Size2MiB>::range(
            PhysFrame::from_start_address(PhysAddr::new(0x0200000)).unwrap(),
            PhysFrame::from_start_address(PhysAddr::new(0x2200000)).unwrap(),
        )
        .pvalidate(Validation::Validated)
        .unwrap();
    }

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
