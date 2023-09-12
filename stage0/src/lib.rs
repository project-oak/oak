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
#![feature(allocator_api)]

extern crate alloc;

use crate::{sev::GHCB_WRAPPER, smp::AP_JUMP_TABLE};
use alloc::boxed::Box;
use core::{arch::asm, ffi::c_void, mem::MaybeUninit, panic::PanicInfo};
use linked_list_allocator::LockedHeap;
use oak_sev_guest::{io::PortFactoryWrapper, msr::SevStatus};
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
use zerocopy::AsBytes;

mod acpi;
mod acpi_tables;
mod allocator;
mod apic;
mod cmos;
mod dice_attestation;
mod fw_cfg;
mod initramfs;
mod kernel;
mod logging;
mod msr;
pub mod paging;
mod pic;
mod sev;
mod smp;
mod zero_page;

type Measurement = [u8; 32];

// Reserve 128K for boot data structures that will outlive Stage 0.
static BOOT_ALLOC: allocator::BumpAllocator<0x20000> = allocator::BumpAllocator::uninit();

// Heap for short-term allocations. These allocations are not expected to outlive Stage 0.
#[cfg_attr(not(test), global_allocator)]
static SHORT_TERM_ALLOC: LockedHeap = LockedHeap::empty();

#[link_section = ".boot"]
#[no_mangle]
static mut SEV_SECRETS: MaybeUninit<oak_sev_guest::secrets::SecretsPage> = MaybeUninit::uninit();
#[link_section = ".boot"]
#[no_mangle]
static SEV_CPUID: MaybeUninit<oak_sev_guest::cpuid::CpuidPage> = MaybeUninit::uninit();

// Will be set in the bootstrap assembly code where we have to read the MSR anyway.
#[no_mangle]
static mut SEV_STATUS: SevStatus = SevStatus::empty();

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

/// Returns the value of the SEV_STATUS MSR that's safe to read even if the CPU doesn't support it.
///
/// Initialized in the bootstrap assembly code.
pub fn sev_status() -> SevStatus {
    // Safety: we don't allow mutation and this is initialized in the bootstrap assembly.
    unsafe { SEV_STATUS }
}

/// Entry point for the Rust code in the stage0 BIOS.
///
/// # Arguments
///
/// * `encrypted` - If not zero, the `encrypted`-th bit will be set in the page tables.
pub fn rust64_start(encrypted: u64) -> ! {
    // We assume 0-th bit is never the encrypted bit.
    let encrypted = if encrypted > 0 { 1 << encrypted } else { 0 };

    paging::init_page_table_refs(encrypted);

    // If we're under SEV-ES or SNP, we need a GHCB block for communication (SNP implies SEV-ES).
    if sev_status().contains(SevStatus::SEV_ES_ENABLED) {
        // No point in calling expect() here, the logging isn't set up yet.
        // In any case, this allocation should not fail. This is the first thing we allocate, the
        // GHCB is 4K in size, and the allocator should be far bigger than that (as we have more
        // data structures we need to allocate in there).
        // If the allocation does fail, something is horribly broken and we have no hope of
        // continuing.
        let ghcb = Box::leak(Box::new_in(sev::Ghcb::new(), &BOOT_ALLOC));
        sev::init_ghcb(ghcb);
    }

    logging::init_logging();
    log::info!("starting...");
    log::info!("Enabled SEV features: {:?}", sev_status());

    let dma_buf = Box::leak(Box::new_in(fw_cfg::DmaBuffer::default(), &BOOT_ALLOC));
    let dma_buf_address = VirtAddr::from_ptr(dma_buf as *const _);
    let dma_access = Box::leak(Box::new_in(fw_cfg::FwCfgDmaAccess::default(), &BOOT_ALLOC));
    let dma_access_address = VirtAddr::from_ptr(dma_access as *const _);
    if sev_status().contains(SevStatus::SEV_ENABLED) {
        // Safety: This is safe for SEV-ES and SNP because we're using an originally supported mode
        // of the Pentium 6: Write-protect, with MTRR enabled.  If we get CPUID reads
        // working, we may want to check that MTRR is supported, but only if we want to
        // support very old processors. However, note that, this branch is only executed if
        // we have encryption, and this wouldn't be true for very old processors.
        unsafe {
            msr::MTRRDefType::write(msr::MTRRDefTypeFlags::MTRR_ENABLE, msr::MemoryType::WP);
        }
        sev::share_page(Page::containing_address(dma_buf_address));
        sev::share_page(Page::containing_address(dma_access_address));
    }

    // Safety: we assume there won't be any other hardware devices using the fw_cfg IO ports.
    let mut fwcfg =
        unsafe { fw_cfg::FwCfg::new(dma_buf, dma_access) }.expect("fw_cfg device not found!");

    let zero_page = Box::leak(Box::new_in(zero_page::ZeroPage::new(), &BOOT_ALLOC));

    zero_page.fill_e820_table(&mut fwcfg);

    if sev_status().contains(SevStatus::SNP_ACTIVE) {
        sev::validate_memory(zero_page.e820_table(), encrypted);
    }

    /* Set up the machine according to the 64-bit Linux boot protocol.
     * See https://www.kernel.org/doc/html/latest/x86/boot.html#id1 for the particular requirements.
     */

    let gdt = Box::leak(Box::new_in(GlobalDescriptorTable::new(), &BOOT_ALLOC));

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

    let idt = Box::leak(Box::new_in(InterruptDescriptorTable::new(), &BOOT_ALLOC));

    create_idt(idt);
    idt.load();

    paging::map_additional_memory(encrypted);

    // Initialize the short-term heap. Any allocations that rely on a global allocator before this
    // point will fail.
    allocator::init_global_allocator(zero_page.e820_table());

    let setup_data_measurement = zero_page
        .try_fill_hdr_from_setup_data(&mut fwcfg)
        .unwrap_or_default();

    if sev_status().contains(SevStatus::SNP_ACTIVE) {
        // Safety: we're only interested in the pointer value of SEV_SECRETS, not its contents.
        let cc_blob = Box::leak(Box::new_in(
            oak_linux_boot_params::CCBlobSevInfo::new(
                unsafe { SEV_SECRETS.as_ptr() },
                SEV_CPUID.as_ptr(),
            ),
            &BOOT_ALLOC,
        ));
        let setup_data = Box::leak(Box::new_in(
            oak_linux_boot_params::CCSetupData::new(cc_blob),
            &BOOT_ALLOC,
        ));

        zero_page.add_setup_data(setup_data);
    }

    let cmdline_measurement = kernel::try_load_cmdline(&mut fwcfg)
        .map(|cmdline| {
            zero_page.set_cmdline(cmdline);
            measure_byte_slice(cmdline.to_bytes())
        })
        .unwrap_or_default();

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

    let mut acpi_digest = Sha256::default();
    let rsdp = acpi::build_acpi_tables(&mut fwcfg, &mut acpi_digest).unwrap();
    zero_page.set_acpi_rsdp_addr(PhysAddr::new(rsdp as *const _ as u64));
    let acpi_digest = acpi_digest.finalize();
    let mut acpi_measurement = Measurement::default();
    acpi_measurement[..].copy_from_slice(&acpi_digest[..]);

    if let Err(err) = smp::bootstrap_aps(rsdp) {
        log::warn!(
            "Failed to bootstrap APs: {}. APs may not be properly initialized.",
            err
        );
    }

    // Register the AP Jump Table, if required.
    if sev_status().contains(SevStatus::SEV_ES_ENABLED) {
        // This assumes identity mapping. Which we have in stage0.
        let jump_table_pa = AP_JUMP_TABLE.as_ptr() as u64;
        if sev_status().contains(SevStatus::SNP_ACTIVE) {
            // Under SNP we need to place the jump table address in the secrets page.
            // Safety: we don't care about the contents of the secrets page beyond writing our jump
            // table address into it.
            let secrets = unsafe { SEV_SECRETS.assume_init_mut() };
            secrets.guest_area_0.ap_jump_table_pa = jump_table_pa;
        } else {
            // Plain old SEV-ES, use the GHCB protocol.
            if let Some(ghcb) = GHCB_WRAPPER.get() {
                ghcb.lock()
                    .set_ap_jump_table(PhysAddr::new(jump_table_pa))
                    .expect("failed to set AP Jump Table");
            }
        }
    }

    let ram_disk_measurement =
        initramfs::try_load_initial_ram_disk(&mut fwcfg, zero_page.e820_table(), &kernel_info)
            .map(|ram_disk| {
                zero_page.set_initial_ram_disk(ram_disk);
                measure_byte_slice(ram_disk)
            })
            .unwrap_or_default();

    let memory_map_measurement = measure_byte_slice(zero_page.e820_table().as_bytes());

    log::debug!("Kernel image digest: {:?}", kernel_info.measurement);
    log::debug!("Kernel setup data digest: {:?}", setup_data_measurement);
    log::debug!("Kernel image digest: {:?}", cmdline_measurement);
    log::debug!("Initial RAM disk digest: {:?}", ram_disk_measurement);
    log::debug!("ACPI table generation digest: {:?}", acpi_measurement);
    log::debug!("E820 table digest: {:?}", memory_map_measurement);

    let measurements = dice_attestation::Measurements {
        acpi_measurement: acpi_measurement,
        kernel_measurement: kernel_info.measurement,
        cmdline_measurement: cmdline_measurement,
        ram_disk_measurement: ram_disk_measurement,
        setup_data_measurement: setup_data_measurement,
        memory_map_measurement: memory_map_measurement,
    };

    dice_attestation::generate_stage1_attestation(&measurements);

    log::info!("jumping to kernel at {:#018x}", entry.as_u64());

    // Clean-ups we need to do just before we jump to the kernel proper: clean up the early GHCB and
    // FW_CFG DMA buffers we used, and switch back to a hugepage for the first 2M of memory.
    if sev_status().contains(SevStatus::SNP_ACTIVE) {
        sev::unshare_page(Page::containing_address(dma_buf_address));
        sev::unshare_page(Page::containing_address(dma_access_address));
        if GHCB_WRAPPER.get().is_some() {
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

/// Calculates the SHA2-256 digest of `source`.
fn measure_byte_slice(source: &[u8]) -> Measurement {
    let mut measurement = Measurement::default();
    let mut digest = Sha256::default();
    digest.update(source);
    let digest = digest.finalize();
    measurement[..].copy_from_slice(&digest[..]);
    measurement
}

/// Creates a factory for accessing raw I/O ports.
fn io_port_factory() -> PortFactoryWrapper {
    if let Some(ghcb) = GHCB_WRAPPER.get() {
        PortFactoryWrapper::new_ghcb(ghcb)
    } else {
        PortFactoryWrapper::new_raw()
    }
}
