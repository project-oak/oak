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
#![feature(slice_ptr_get)]

extern crate alloc;

use alloc::{boxed::Box, format, string::String, vec::Vec};
use core::{arch::asm, ffi::c_void, panic::PanicInfo};

use linked_list_allocator::LockedHeap;
use oak_dice::evidence::DICE_DATA_CMDLINE_PARAM;
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use oak_proto_rust::oak::attestation::v1::{Event, EventLog, Stage0Measurements};
use prost::Message;
use sha2::{Digest, Sha256};
use x86_64::{
    instructions::{hlt, interrupts::int3},
    registers::segmentation::*,
    structures::{
        gdt::{Descriptor, GlobalDescriptorTable},
        idt::InterruptDescriptorTable,
        paging::{PageSize, Size1GiB},
    },
    PhysAddr, VirtAddr,
};
use zerocopy::AsBytes;

use crate::{alloc::string::ToString, kernel::KernelType};

mod acpi;
mod acpi_tables;
mod allocator;
mod apic;
mod cmos;
mod fw_cfg;
mod hal;
mod initramfs;
mod kernel;
mod logging;
mod msr;
pub mod paging;
mod pic;
mod smp;
mod zero_page;

type Measurement = [u8; 32];

// Reserve 128K for boot data structures that will outlive Stage 0.
type BootAllocator = allocator::BumpAllocator<0x20000>;
static BOOT_ALLOC: BootAllocator = BootAllocator::uninit();

// Heap for short-term allocations. These allocations are not expected to
// outlive Stage 0.
#[cfg_attr(not(test), global_allocator)]
static SHORT_TERM_ALLOC: LockedHeap = LockedHeap::empty();

/// We create an identity map for the first 1GiB of memory.
const TOP_OF_VIRTUAL_MEMORY: u64 = Size1GiB::SIZE;

const PAGE_SIZE: usize = 4096;

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

/// Passes control to the operating system kernel. No more code from the BIOS
/// will run.
///
/// # Safety
///
/// This assumes that the kernel entry point is valid.
pub unsafe fn jump_to_kernel<A: core::alloc::Allocator>(
    entry_point: VirtAddr,
    zero_page: Box<zero_page::ZeroPage, &A>,
) -> ! {
    asm!(
        // Boot stack pointer
        "mov {1}, %rsp",
        // Zero page address
        "mov {2}, %rsi",
        // ...and away we go!
        "jmp *{0}",
        in(reg) entry_point.as_u64(),
        in(reg) &BOOT_STACK_POINTER as *const _ as u64,
        in(reg) Box::leak(zero_page),
        options(noreturn, att_syntax)
    );
}

/// Entry point for the Rust code in the stage0 BIOS.
///
/// # Arguments
///
/// * `encrypted` - If not zero, the `encrypted`-th bit will be set in the page
///   tables.
pub fn rust64_start() -> ! {
    paging::init_page_table_refs();
    hal::early_initialize_platform();
    logging::init_logging();
    log::info!("starting...");
    // Safety: we assume there won't be any other hardware devices using the fw_cfg
    // IO ports.
    let mut fwcfg = unsafe { fw_cfg::FwCfg::new(&BOOT_ALLOC) }.expect("fw_cfg device not found!");

    let mut zero_page = Box::new_in(zero_page::ZeroPage::new(), &BOOT_ALLOC);

    zero_page.fill_e820_table(&mut fwcfg);

    hal::initialize_platform(zero_page.e820_table());

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

    paging::map_additional_memory();

    // Initialize the short-term heap. Any allocations that rely on a global
    // allocator before this point will fail.
    allocator::init_global_allocator(zero_page.e820_table());

    let setup_data_sha2_256_digest =
        zero_page.try_fill_hdr_from_setup_data(&mut fwcfg).unwrap_or_default();

    hal::populate_zero_page(&mut zero_page);

    let cmdline = kernel::try_load_cmdline(&mut fwcfg).unwrap_or_default();
    let cmdline_sha2_256_digest = cmdline.measure();

    let kernel_info =
        kernel::try_load_kernel_image(&mut fwcfg, zero_page.e820_table()).unwrap_or_default();
    let mut entry = kernel_info.entry;

    // Attempt to parse 64 bytes at the suggested entry point as an ELF header. If
    // it works, extract the entry point address from there; if there is no
    // valid ELF header at that address, assume it's code, and jump there
    // directly. Safety: this assumes the kernel is loaded at the given address.
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
    let mut acpi_sha2_256_digest = Measurement::default();
    acpi_sha2_256_digest[..].copy_from_slice(&acpi_digest[..]);

    if let Err(err) = smp::bootstrap_aps(rsdp) {
        log::warn!("Failed to bootstrap APs: {}. APs may not be properly initialized.", err);
    }

    let ram_disk_sha2_256_digest =
        initramfs::try_load_initial_ram_disk(&mut fwcfg, zero_page.e820_table(), &kernel_info)
            .map(|ram_disk| {
                zero_page.set_initial_ram_disk(ram_disk);
                ram_disk.measure()
            })
            .unwrap_or_default();

    // QEMU assumes all SEV VMs use OVMF, and leaves type_of_loader 0x00. This
    // would make the kernel unable to load stage1. We need to fix it to make
    // stage1 loads smoothly.
    zero_page.set_type_of_loader(zero_page::BOOT_LOADER_TYPE_UNDEFINED);

    let memory_map_sha2_256_digest = zero_page.e820_table().measure();

    // Generate Stage0 Event Log data.
    let stage0event = oak_proto_rust::oak::attestation::v1::Stage0Measurements {
        kernel_measurement: kernel_info.measurement.as_bytes().to_vec(),
        acpi_digest: acpi_sha2_256_digest.as_bytes().to_vec(),
        memory_map_digest: memory_map_sha2_256_digest.as_bytes().to_vec(),
        ram_disk_digest: ram_disk_sha2_256_digest.as_bytes().to_vec(),
        setup_data_digest: setup_data_sha2_256_digest.as_bytes().to_vec(),
        kernel_cmdline: cmdline.clone(),
    };

    let event_log_proto = generate_event_log(stage0event);
    let eventlog_sha2_256_digest = event_log_proto.encoded_events[0].measure();

    log::debug!("Kernel image digest: sha2-256:{}", hex::encode(kernel_info.measurement));
    log::debug!("Kernel setup data digest: sha2-256:{}", hex::encode(setup_data_sha2_256_digest));
    log::debug!("Kernel command-line: {}", cmdline);
    log::debug!("Initial RAM disk digest: sha2-256:{}", hex::encode(ram_disk_sha2_256_digest));
    log::debug!("ACPI table generation digest: sha2-256:{}", hex::encode(acpi_sha2_256_digest));
    log::debug!("E820 table digest: sha2-256:{}", hex::encode(memory_map_sha2_256_digest));
    log::debug!("Event Log digest: sha2-256:{}", hex::encode(eventlog_sha2_256_digest));

    // TODO: b/331252282 - Remove temporary workaround for cmd line length.
    let cmdline_max_len = 256;
    let measurements = oak_stage0_dice::Measurements {
        acpi_sha2_256_digest,
        kernel_sha2_256_digest: kernel_info.measurement,
        cmdline_sha2_256_digest,
        cmdline: if cmdline.len() > cmdline_max_len {
            cmdline[..cmdline_max_len].to_string()
        } else {
            cmdline.clone()
        },
        ram_disk_sha2_256_digest,
        setup_data_sha2_256_digest,
        memory_map_sha2_256_digest,
        eventlog_sha2_256_digest,
    };

    let tee_platform = hal::tee_platform();

    let dice_data = Box::leak(Box::new_in(
        oak_stage0_dice::generate_dice_data(
            &measurements,
            hal::get_attestation,
            hal::get_derived_key,
            tee_platform,
        ),
        &crate::BOOT_ALLOC,
    ));
    // Reserve the memory containing the DICE data.
    zero_page.insert_e820_entry(BootE820Entry::new(
        dice_data.as_bytes().as_ptr() as usize,
        dice_data.as_bytes().len(),
        E820EntryType::RESERVED,
    ));

    // Write Eventlog data to memory.
    let mut event_log = Vec::with_capacity_in(PAGE_SIZE, &crate::BOOT_ALLOC);
    // Ensure that Eventlog is not too big. The 8 bytes are reserved for the size of
    // the encoded eventlog proto.
    assert!(event_log_proto.encoded_len() < PAGE_SIZE - 8);
    // First copy the size of the encoded proto in Little Endian format. Then copy
    // the actual EventLog.
    event_log.extend_from_slice(event_log_proto.encoded_len().to_le_bytes().as_slice());
    event_log.extend_from_slice(event_log_proto.encode_to_vec().as_bytes());
    let event_log_data = event_log.leak();
    // Reserve memory containing Eventlog Data.
    zero_page.insert_e820_entry(BootE820Entry::new(
        event_log_data.as_bytes().as_ptr() as usize,
        PAGE_SIZE,
        E820EntryType::RESERVED,
    ));

    // Append the DICE data address to the kernel command-line.
    let extra = format!("--{DICE_DATA_CMDLINE_PARAM}={dice_data:p}");
    let cmdline = if kernel_info.kernel_type == KernelType::Elf {
        // Current systems that use the ELF kernel does not support DICE data, so don't
        // append the extra parameter.
        cmdline
    } else if cmdline.is_empty() {
        extra
    } else if cmdline.contains("--") {
        format!("{} {}", cmdline, extra)
    } else {
        format!("{} -- {}", cmdline, extra)
    };
    zero_page.set_cmdline(cmdline);

    log::info!("jumping to kernel at {:#018x}", entry.as_u64());

    // Clean-ups we need to do just before we jump to the kernel proper: clean up
    // the early GHCB and FW_CFG DMA buffers we used, and switch back to a
    // hugepage for the first 2M of memory.
    drop(fwcfg);
    // After the call to `deinit_platform`:
    //  - Do not log anything any more.
    //  - Do not allocate memory.
    hal::deinit_platform();
    paging::remap_first_huge_page();

    unsafe {
        jump_to_kernel(entry, zero_page);
    }
}

/// Common panic routine for the Stage0 binaries. This needs to be wrapped in a
/// panic_handler function in individual binary crates.
pub fn panic(info: &PanicInfo) -> ! {
    log::error!("{}", info);

    // Trigger a breakpoint exception. As we don't have a #BP handler, this will
    // triple fault and terminate the program.
    int3();

    loop {
        hlt();
    }
}

fn phys_to_virt(address: PhysAddr) -> VirtAddr {
    // We use an identity mapping throughout.
    VirtAddr::new(address.as_u64())
}

trait Measured {
    /// Calculates the SHA2-256 digest of `source`.
    fn measure(&self) -> Measurement;
}

impl<T: zerocopy::AsBytes + ?Sized> Measured for T {
    fn measure(&self) -> Measurement {
        let mut measurement = Measurement::default();
        let mut digest = Sha256::default();
        digest.update(self.as_bytes());
        let digest = digest.finalize();
        measurement[..].copy_from_slice(&digest[..]);
        measurement
    }
}

fn generate_event_log(measurements: Stage0Measurements) -> EventLog {
    let tag = String::from("Stage0");
    let any = prost_types::Any::from_msg(&measurements);
    let event = Event { tag, event: Some(any.unwrap()) };
    log::info!("Any:{:?}", event.event.clone().unwrap());
    let mut eventlog = EventLog::default();
    eventlog.encoded_events.push(event.encode_to_vec());
    eventlog
}
