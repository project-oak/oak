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

use alloc::{boxed::Box, format, vec::Vec};
use core::panic::PanicInfo;

use linked_list_allocator::LockedHeap;
use oak_dice::evidence::{
    DICE_DATA_CMDLINE_PARAM, DICE_DATA_LENGTH_CMDLINE_PARAM, EVENTLOG_CMDLINE_PARAM,
    STAGE0_DICE_PROTO_MAGIC,
};
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
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

use crate::alloc::string::ToString;

mod acpi;
mod acpi_tables;
mod allocator;
mod apic;
mod cmos;
mod fw_cfg;
pub mod hal;
mod initramfs;
mod kernel;
mod logging;
mod msr;
pub mod paging;
mod pic;
mod smp;
mod zero_page;

pub use hal::Platform;
#[cfg(feature = "sev")]
pub use hal::Sev;
pub use zero_page::ZeroPage;

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

pub fn create_gdt(gdt: &mut GlobalDescriptorTable) -> (SegmentSelector, SegmentSelector) {
    let cs = gdt.add_entry(Descriptor::kernel_code_segment());
    let ds = gdt.add_entry(Descriptor::kernel_data_segment());
    (cs, ds)
}

pub fn create_idt(_idt: &mut InterruptDescriptorTable) {}

/// Entry point for the Rust code in the stage0 BIOS.
///
/// # Arguments
///
/// * `encrypted` - If not zero, the `encrypted`-th bit will be set in the page
///   tables.
pub fn rust64_start<P: hal::Platform>() -> ! {
    paging::init_page_table_refs::<P>();
    P::early_initialize_platform();
    logging::init_logging::<P>();
    log::info!("starting...");
    // Safety: we assume there won't be any other hardware devices using the fw_cfg
    // IO ports.
    let mut fwcfg = unsafe { fw_cfg::FwCfg::new(&BOOT_ALLOC) }.expect("fw_cfg device not found!");

    let mut zero_page = Box::new_in(zero_page::ZeroPage::new(), &BOOT_ALLOC);

    zero_page.fill_e820_table::<P>(&mut fwcfg);

    P::initialize_platform(zero_page.e820_table());

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

    paging::map_additional_memory::<P>();

    // Initialize the short-term heap. Any allocations that rely on a global
    // allocator before this point will fail.
    allocator::init_global_allocator(zero_page.e820_table());

    let setup_data_sha2_256_digest =
        zero_page.try_fill_hdr_from_setup_data(&mut fwcfg).unwrap_or_default();

    P::populate_zero_page(&mut zero_page);

    let cmdline = kernel::try_load_cmdline(&mut fwcfg).unwrap_or_default();
    let cmdline_sha2_256_digest = cmdline.measure();

    // Safety: this is the only place where we try to load a kernel, so the backing
    // memory is unused.
    let kernel = unsafe { kernel::Kernel::try_load_kernel_image(&mut fwcfg) }.unwrap();
    let kernel_sha2_256_digest = kernel.measure();

    let mut acpi_digest = Sha256::default();
    let rsdp = acpi::build_acpi_tables(&mut fwcfg, &mut acpi_digest).unwrap();
    zero_page.set_acpi_rsdp_addr(PhysAddr::new(rsdp as *const _ as u64));
    let acpi_digest = acpi_digest.finalize();
    let mut acpi_sha2_256_digest = Measurement::default();
    acpi_sha2_256_digest[..].copy_from_slice(&acpi_digest[..]);

    if let Err(err) = smp::bootstrap_aps::<P>(rsdp) {
        log::warn!("Failed to bootstrap APs: {}. APs may not be properly initialized.", err);
    }

    let ram_disk_sha2_256_digest =
        initramfs::try_load_initial_ram_disk(&mut fwcfg, zero_page.e820_table(), &kernel)
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
    let (event_log_proto, event_sha2_256_digest) = oak_stage0_dice::generate_event_log(
        kernel_sha2_256_digest.as_bytes().to_vec(),
        acpi_sha2_256_digest.as_bytes().to_vec(),
        memory_map_sha2_256_digest.as_bytes().to_vec(),
        ram_disk_sha2_256_digest.as_bytes().to_vec(),
        setup_data_sha2_256_digest.as_bytes().to_vec(),
        cmdline.clone(),
    );

    log::debug!("Kernel image digest: sha2-256:{}", hex::encode(kernel_sha2_256_digest));
    log::debug!("Kernel setup data digest: sha2-256:{}", hex::encode(setup_data_sha2_256_digest));
    log::debug!("Kernel command-line: {}", cmdline);
    log::debug!("Initial RAM disk digest: sha2-256:{}", hex::encode(ram_disk_sha2_256_digest));
    log::debug!("ACPI table generation digest: sha2-256:{}", hex::encode(acpi_sha2_256_digest));
    log::debug!("E820 table digest: sha2-256:{}", hex::encode(memory_map_sha2_256_digest));
    log::debug!("Event digest: sha2-256:{}", hex::encode(event_sha2_256_digest));

    // TODO: b/331252282 - Remove temporary workaround for cmd line length.
    let cmdline_max_len = 256;
    let measurements = oak_stage0_dice::Measurements {
        acpi_sha2_256_digest,
        kernel_sha2_256_digest,
        cmdline_sha2_256_digest,
        cmdline: if cmdline.len() > cmdline_max_len {
            cmdline[..cmdline_max_len].to_string()
        } else {
            cmdline.clone()
        },
        ram_disk_sha2_256_digest,
        setup_data_sha2_256_digest,
        memory_map_sha2_256_digest,
        event_sha2_256_digest,
    };

    let tee_platform = P::tee_platform();

    let (dice_data_struct, dice_data_proto) = oak_stage0_dice::generate_dice_data(
        &measurements,
        P::get_attestation,
        P::get_derived_key,
        tee_platform,
        event_log_proto.clone(),
    );
    let dice_data = Box::leak(Box::new_in(dice_data_struct, &crate::BOOT_ALLOC));

    // Reserve the memory containing the DICE data.
    zero_page.insert_e820_entry(BootE820Entry::new(
        dice_data.as_bytes().as_ptr() as usize,
        dice_data.as_bytes().len(),
        E820EntryType::RESERVED,
    ));
    let mut sensitive_dice_data_length = core::mem::size_of::<oak_dice::evidence::Stage0DiceData>();

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
    sensitive_dice_data_length += PAGE_SIZE;

    // TODO: b/360223468 - Combine the DiceData proto with the EventLog Proto and
    // write all of it in memory.
    // Write DiceData protobuf bytes to memory.
    let mut encoded_dice_proto = Vec::with_capacity_in(PAGE_SIZE, &crate::BOOT_ALLOC);
    // Ensure that DiceData proto bytes is not too big. The 8 bytes are reserved for
    // the size of the encoded DiceData proto.
    assert!(dice_data_proto.encoded_len() < PAGE_SIZE - 8 * 2);
    // Insert a magic number to ensure the correctness of the data being read.
    encoded_dice_proto.extend_from_slice(STAGE0_DICE_PROTO_MAGIC.to_le_bytes().as_slice());
    encoded_dice_proto.extend_from_slice(dice_data_proto.encoded_len().to_le_bytes().as_slice());
    encoded_dice_proto.extend_from_slice(dice_data_proto.encode_to_vec().as_bytes());

    // Reserve memory containing DICE proto Data.
    zero_page.insert_e820_entry(BootE820Entry::new(
        encoded_dice_proto.as_bytes().as_ptr() as usize,
        PAGE_SIZE,
        E820EntryType::RESERVED,
    ));
    sensitive_dice_data_length += PAGE_SIZE;

    // Append the DICE data address to the kernel command-line.
    let extra = format!(
        "--{DICE_DATA_CMDLINE_PARAM}={dice_data:p} --{EVENTLOG_CMDLINE_PARAM}={event_log_data:p} --{DICE_DATA_LENGTH_CMDLINE_PARAM}={sensitive_dice_data_length}"
    );
    let cmdline = if cmdline.is_empty() {
        extra
    } else if cmdline.contains("--") {
        format!("{} {}", cmdline, extra)
    } else {
        format!("{} -- {}", cmdline, extra)
    };
    zero_page.set_cmdline(cmdline);

    log::info!("jumping to kernel at {:#018x}", kernel.entry().as_u64());

    // Clean-ups we need to do just before we jump to the kernel proper: clean up
    // the early GHCB and FW_CFG DMA buffers we used, and switch back to a
    // hugepage for the first 2M of memory.
    drop(fwcfg);
    // After the call to `deinit_platform`:
    //  - Do not log anything any more.
    //  - Do not allocate memory.
    P::deinit_platform();
    paging::remap_first_huge_page::<P>();

    unsafe {
        kernel.jump_to_kernel(zero_page);
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
