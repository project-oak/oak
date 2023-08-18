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
#![feature(int_roundings)]

use core::{arch::asm, ffi::c_void, mem::MaybeUninit, panic::PanicInfo};
use oak_sev_guest::io::PortFactoryWrapper;
use sha2::{Digest, Sha256};
use x86_64::{
    instructions::{hlt, interrupts::int3, segmentation::Segment},
    registers::segmentation::*,
    structures::{
        gdt::{Descriptor, GlobalDescriptorTable, SegmentSelector},
        idt::InterruptDescriptorTable,
        paging::{Page, PageSize, Size1GiB},
    },
    PhysAddr, VirtAddr,
};

mod acpi;
mod alloc;
mod cmos;
mod fw_cfg;
mod initramfs;
mod kernel;
mod logging;
pub mod paging;
mod sev;
mod smp;
mod zero_page;

// Reserve 128K for boot data structures.
static BOOT_ALLOC: alloc::Allocator<0x20000> = alloc::Allocator::uninit();

#[link_section = ".boot"]
#[no_mangle]
static SEV_SECRETS: MaybeUninit<oak_sev_guest::secrets::SecretsPage> = MaybeUninit::uninit();
#[link_section = ".boot"]
#[no_mangle]
static SEV_CPUID: MaybeUninit<oak_sev_guest::cpuid::CpuidPage> = MaybeUninit::uninit();

/// We create an identity map for the first 1GiB of memory.
const TOP_OF_VIRTUAL_MEMORY: u64 = Size1GiB::SIZE;

extern "C" {
    #[link_name = "stack_start"]
    static BOOT_STACK_POINTER: c_void;
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
pub unsafe fn jump_to_kernel(entry_point: VirtAddr, zero_page: usize) -> ! {
    asm!(
        // Boot stack pointer
        "mov {1}, %rsp",
        // Zero page address
        "mov {2}, %rsi",
        // ...and away we go!
        "jmp *{0}",
        in(reg) entry_point.as_u64(),
        in(reg) &BOOT_STACK_POINTER as *const _ as u64,
        in(reg) zero_page as u64,
        options(noreturn, att_syntax)
    );
}

/// Entry point for the Rust code in the stage0 BIOS.
///
/// # Arguments
///
/// * `encrypted` - If not zero, the `encrypted`-th bit will be set in the page tables.
pub fn rust64_start(encrypted: u64) -> ! {
    let (es, snp) = if encrypted > 0 {
        // We're under some form of memory encryption, thus it's safe to access the SEV_STATUS MSR.
        let status =
            oak_sev_guest::msr::get_sev_status().unwrap_or(oak_sev_guest::msr::SevStatus::empty());
        (
            status.contains(oak_sev_guest::msr::SevStatus::SEV_ES_ENABLED),
            status.contains(oak_sev_guest::msr::SevStatus::SNP_ACTIVE),
        )
    } else {
        (false, false)
    };

    // We assume 0-th bit is never the encrypted bit.
    let encrypted = if encrypted > 0 { 1 << encrypted } else { 0 };

    paging::init_page_table_refs(encrypted);

    // If we're under SEV-ES or SNP, we need a GHCB block for communication (SNP implies SEV-ES).
    let ghcb_protocol = if es {
        // No point in calling expect() here, the logging isn't set up yet.
        // In any case, this allocation should not fail. This is the first thing we allocate, the
        // GHCB is 4K in size, and the allocator should be far bigger than that (as we have more
        // data structures we need to allocate in there).
        // If the allocation does fail, something is horribly broken and we have no hope of
        // continuing.
        let ghcb = BOOT_ALLOC.leak(sev::Ghcb::new()).unwrap();
        Some(sev::init_ghcb(ghcb, snp))
    } else {
        None
    };

    logging::init_logging(match ghcb_protocol {
        Some(protocol) => PortFactoryWrapper::new_ghcb(protocol),
        None => PortFactoryWrapper::new_raw(),
    });
    log::info!("starting...");

    let dma_buf = BOOT_ALLOC.leak(fw_cfg::DmaBuffer::default()).unwrap();
    let dma_buf_address = VirtAddr::from_ptr(dma_buf as *const _);
    let dma_access = BOOT_ALLOC.leak(fw_cfg::FwCfgDmaAccess::default()).unwrap();
    let dma_access_address = VirtAddr::from_ptr(dma_access as *const _);
    if encrypted > 0 {
        // Safety: This is safe for SEV-ES and SNP because we're using an originally supported mode
        // of the Pentium 6: Write-protect, with MTRR enabled.  If we get CPUID reads
        // working, we may want to check that MTRR is supported, but only if we want to
        // support very old processors. However, note that, this branch is only executed if
        // we have encryption, and this wouldn't be true for very old processors.
        unsafe {
            sev::MTRRDefType::write(sev::MTRRDefTypeFlags::MTRR_ENABLE, sev::MemoryType::WP);
        }
        sev::share_page(Page::containing_address(dma_buf_address), snp);
        sev::share_page(Page::containing_address(dma_access_address), snp);
    }

    // Safety: we assume there won't be any other hardware devices using the fw_cfg IO ports.
    let mut fwcfg = unsafe {
        fw_cfg::FwCfg::new(
            match ghcb_protocol {
                Some(protocol) => PortFactoryWrapper::new_ghcb(protocol),
                None => PortFactoryWrapper::new_raw(),
            },
            dma_buf,
            dma_access,
        )
    }
    .expect("fw_cfg device not found!");

    let zero_page = BOOT_ALLOC
        .leak(zero_page::ZeroPage::new())
        .expect("failed to allocate memory for zero page");

    zero_page.fill_e820_table(
        &mut fwcfg,
        match ghcb_protocol {
            Some(protocol) => PortFactoryWrapper::new_ghcb(protocol),
            None => PortFactoryWrapper::new_raw(),
        },
    );

    if snp {
        sev::validate_memory(zero_page.e820_table(), encrypted);
    }

    /* Set up the machine according to the 64-bit Linux boot protocol.
     * See https://www.kernel.org/doc/html/latest/x86/boot.html#id1 for the particular requirements.
     */

    let gdt = BOOT_ALLOC
        .leak(GlobalDescriptorTable::new())
        .expect("Failed to allocate memory for GDT");

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

    let idt = BOOT_ALLOC
        .leak(InterruptDescriptorTable::new())
        .expect("Failed to allocate memory for IDT");

    create_idt(idt);
    idt.load();

    paging::map_additional_memory(encrypted);

    let setup_data_measurement = zero_page.try_fill_hdr_from_setup_data(&mut fwcfg);

    if snp {
        let cc_blob = BOOT_ALLOC
            .leak(oak_linux_boot_params::CCBlobSevInfo::new(
                SEV_SECRETS.as_ptr(),
                SEV_CPUID.as_ptr(),
            ))
            .expect("Failed to allocate memory for CCBlobSevInfo");
        let setup_data = BOOT_ALLOC
            .leak(oak_linux_boot_params::CCSetupData::new(cc_blob))
            .expect("Failed to allocate memory for CCSetupData");

        zero_page.add_setup_data(setup_data);
    }

    let mut cmdline_measurment = [0u8; 32];
    if let Some(cmdline) = kernel::try_load_cmdline(&mut fwcfg) {
        populate_measurement(&mut cmdline_measurment, cmdline.to_bytes());
        zero_page.set_cmdline(cmdline);
    }

    let kernel_info = kernel::try_load_kernel_image(&mut fwcfg, zero_page.e820_table())
        .unwrap_or(kernel::KernelInfo::default());
    let mut entry = kernel_info.entry;

    // Attempt to parse 64 bytes at the suggested entry point as an ELF header. If it works, extract
    // the entry point address from there; if there is no valid ELF header at that address, assume
    // it's code, and jump there directly.
    // Safety: this assumes the kernel is loaded at the given address.
    let header = unsafe { &*(entry.as_u64() as *const elf::file::Elf64_Ehdr) };
    if header.e_ident[0] == elf::abi::ELFMAG0
        && header.e_ident[1] == elf::abi::ELFMAG1
        && header.e_ident[2] == elf::abi::ELFMAG2
        && header.e_ident[3] == elf::abi::ELFMAG3
        && header.e_ident[4] == elf::abi::ELFCLASS64
        && header.e_ident[5] == elf::abi::ELFDATA2LSB
        && header.e_ident[6] == elf::abi::EV_CURRENT
        && header.e_ident[7] == elf::abi::ELFOSABI_SYSV
    {
        // Looks like we have a valid ELF header at 0x200000. Trust its entry point.
        entry = VirtAddr::new(header.e_entry);
    }

    let rsdp = acpi::build_acpi_tables(&mut fwcfg).unwrap();
    zero_page.set_acpi_rsdp_addr(PhysAddr::new(rsdp as *const _ as u64));

    if let Err(err) = smp::bootstrap_aps(rsdp) {
        log::warn!(
            "Failed to bootstrap APs: {}. APs may not be properly initialized.",
            err
        );
    }

    let mut ram_disk_measurment = [0u8; 32];
    if let Some(ram_disk) =
        initramfs::try_load_initial_ram_disk(&mut fwcfg, zero_page.e820_table(), &kernel_info)
    {
        populate_measurement(&mut ram_disk_measurment, ram_disk);
        zero_page.set_initial_ram_disk(ram_disk);
    }

    log::debug!("Kernel image digest: {:?}", kernel_info.measurement);
    log::debug!("Kernel setup data digest: {:?}", setup_data_measurement);
    log::debug!("Kernel image digest: {:?}", cmdline_measurment);
    log::debug!("Initial RAM disk digest: {:?}", ram_disk_measurment);

    log::info!("jumping to kernel at {:#018x}", entry.as_u64());

    // Clean-ups we need to do just before we jump to the kernel proper: clean up the early GHCB and
    // FW_CFG DMA buffers we used, and switch back to a hugepage for the first 2M of memory.
    if snp {
        sev::unshare_page(Page::containing_address(dma_buf_address));
        sev::unshare_page(Page::containing_address(dma_access_address));
        if ghcb_protocol.is_some() {
            sev::deinit_ghcb();
        }
    }
    paging::remap_first_huge_page(encrypted);

    unsafe {
        jump_to_kernel(entry, zero_page as *const _ as usize);
    }
}

/// Common panic routine for the Stage0 binaries. This needs to be wrapped in a panic_handler
/// function in individual binary crates.
pub fn panic(info: &PanicInfo) -> ! {
    log::error!("{}", info);

    // Trigger a breakpoint exception. As we don't have a #BP handler, this will triple fault and
    // terminate the program.
    int3();

    loop {
        hlt();
    }
}

fn phys_to_virt(address: PhysAddr) -> VirtAddr {
    // We use an identity mapping throughout.
    VirtAddr::new(address.as_u64())
}

/// Overwrites `measurement` with the SHA2-256 digest or `source`.
fn populate_measurement(measurement: &mut [u8; 32], source: &[u8]) {
    let mut digest = Sha256::default();
    digest.update(source);
    let digest = digest.finalize();
    measurement[..].copy_from_slice(&digest[..]);
}
