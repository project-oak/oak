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

#![cfg_attr(not(test), no_std)]
#![feature(int_roundings)]
#![feature(allocator_api)]
#![feature(slice_ptr_get)]
#![feature(let_chains)]
#![allow(static_mut_refs)]

extern crate alloc;

use alloc::{boxed::Box, format, vec::Vec};
use core::panic::PanicInfo;

use linked_list_allocator::LockedHeap;
use oak_attestation_types::{
    transparent_attester::TransparentAttester,
    util::{Serializable, encode_length_delimited_proto, try_decode_length_delimited_proto},
};
use oak_dice::evidence::{
    DICE_DATA_ATTESTATION_PARAM, DICE_DATA_CMDLINE_PARAM, DICE_DATA_LENGTH_CMDLINE_PARAM,
    EVENTLOG_CMDLINE_PARAM, STAGE0_DICE_PROTO_MAGIC,
};
use oak_linux_boot_params::{BootE820Entry, E820EntryType};
use oak_proto_rust::oak::attestation::v1::DiceData;
use oak_stage0_dice::{DerivedKey, derive_sealing_cdi};
use sha2::{Digest, Sha256};
use x86_64::{
    PhysAddr, VirtAddr,
    instructions::{hlt, interrupts::int3},
    registers::segmentation::*,
    structures::{
        gdt::{Descriptor, GlobalDescriptorTable},
        idt::InterruptDescriptorTable,
        paging::{PageSize, Size1GiB, Size4KiB},
    },
};
use zerocopy::IntoBytes;
use zeroize::Zeroize;

mod acpi;
mod acpi_tables;
pub mod allocator;
mod apic;
mod cmos;
mod fw_cfg;
pub mod hal;
mod initramfs;
mod kernel;
mod logging;
pub mod mailbox;
pub mod msr;
pub mod paging;
mod pci;
mod pic;
mod zero_page;

pub use acpi_tables::{
    DescriptionHeader, LocalApicFlags, Madt, MultiprocessorWakeup, ProcessorLocalApic,
    ProcessorLocalX2Apic, Rsdp, Rsdt, RsdtEntryPairMut, Xsdt,
};
pub use apic::Lapic;
pub use hal::Platform;
pub use pic::disable_pic8259;
pub use zero_page::ZeroPage;

type Measurement = [u8; 32];

// Reserve 128K for boot data structures that will outlive Stage 0.
pub type BootAllocator = allocator::BumpAllocator<0x20000>;
pub static BOOT_ALLOC: BootAllocator = BootAllocator::uninit();

// Heap for short-term allocations. These allocations are not expected to
// outlive Stage 0.
#[cfg_attr(all(not(test), not(feature = "stage0_test")), global_allocator)]
pub static SHORT_TERM_ALLOC: LockedHeap = LockedHeap::empty();

/// We create an identity map for the first 1GiB of memory.
const TOP_OF_VIRTUAL_MEMORY: u64 = Size1GiB::SIZE;

// Default memory page size on x86_64.
const PAGE_SIZE: usize = Size4KiB::SIZE as usize;

// Double page size for items larger than the PAGE_SIZE limit.
const DOUBLE_PAGE_SIZE: usize = PAGE_SIZE * 2;

pub fn create_gdt(gdt: &mut GlobalDescriptorTable) -> (SegmentSelector, SegmentSelector) {
    let cs = gdt.append(Descriptor::kernel_code_segment());
    let ds = gdt.append(Descriptor::kernel_data_segment());
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
    let kernel_cmdline = cmdline.kernel_cmdline();

    // Safety: this is the only place where we try to load a kernel, so the backing
    // memory is unused.
    let kernel = unsafe { kernel::Kernel::try_load_kernel_image(&mut fwcfg) }.unwrap();
    let kernel_sha2_256_digest = kernel.measure();

    // Set up the allocator for ACPI-related memory in the EBDA region.
    acpi::setup_low_allocator(&mut zero_page).unwrap();

    // Grab 1 MB of memory for ACPI-related things, as not everything will fit into
    // the EBDA. We want this space to be 1M in size, and to be as close to the 1GiB
    // boundary as possible.
    acpi::setup_high_allocator(&mut zero_page).unwrap();

    // Look into PCI first as we need to know where the PCI memory ranges are before
    // we build the ACPI tables.
    let pci_windows = pci::init::<P>(&mut fwcfg, &mut zero_page).unwrap();

    let mut acpi_digest = Sha256::default();
    let rsdp = acpi::build_acpi_tables(&mut fwcfg, &mut acpi_digest, pci_windows).unwrap();
    zero_page.set_acpi_rsdp_addr(PhysAddr::new(rsdp as *const _ as u64));
    let acpi_digest = acpi_digest.finalize();
    let mut acpi_sha2_256_digest = Measurement::default();
    acpi_sha2_256_digest[..].copy_from_slice(&acpi_digest[..]);

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

    let stage0_event_proto = oak_proto_rust::oak::attestation::v1::Stage0Measurements {
        setup_data_digest: setup_data_sha2_256_digest.as_bytes().to_vec(),
        kernel_measurement: kernel_sha2_256_digest.as_bytes().to_vec(),
        ram_disk_digest: ram_disk_sha2_256_digest.as_bytes().to_vec(),
        memory_map_digest: memory_map_sha2_256_digest.as_bytes().to_vec(),
        acpi_digest: acpi_sha2_256_digest.as_bytes().to_vec(),
        kernel_cmdline: kernel_cmdline.clone(),
    };

    let kernel_commandline_digest = cmdline.measure();

    // Introduce transparent measurements (i.e. measurements that do not contain
    // sensitive data).
    let stage0_transparent_event_proto =
        oak_proto_rust::oak::attestation::v1::Stage0TransparentMeasurements {
            setup_data_digest: stage0_event_proto.setup_data_digest.clone(),
            kernel_measurement: stage0_event_proto.kernel_measurement.clone(),
            ram_disk_digest: stage0_event_proto.ram_disk_digest.clone(),
            memory_map_digest: stage0_event_proto.memory_map_digest.clone(),
            acpi_digest: stage0_event_proto.acpi_digest.clone(),
            kernel_cmdline_digest: kernel_commandline_digest.as_bytes().to_vec(),
        };

    // Use the root derived key as the UDS (unique device secret) for deriving
    // sealing keys.
    let mut uds: DerivedKey = P::get_derived_key().expect("couldn't get derived key");

    let mut cdi = derive_sealing_cdi(&uds, &stage0_event_proto);
    // Zero out the UDS.
    uds.zeroize();

    // Generate Stage0 Event Log data.
    let stage0_event = oak_stage0_dice::encode_stage0_event(stage0_event_proto);
    let event_sha2_256_digest = Sha256::digest(&stage0_event).to_vec();
    let event_log_proto = {
        let mut base = oak_proto_rust::oak::attestation::v1::EventLog::default();
        base.encoded_events.push(stage0_event.to_vec());
        base
    };

    // Generate Stage0 Transparent Event Log data.
    // TODO: b/452735395 - Update the attester to accept the new transparent event.
    let stage0_transparent_event =
        oak_stage0_dice::encode_stage0_transparent_event(stage0_transparent_event_proto);
    let transparent_event_sha2_256_digest = Sha256::digest(&stage0_transparent_event).to_vec();

    log::debug!("Kernel image digest: sha2-256:{}", hex::encode(kernel_sha2_256_digest));
    log::debug!("Kernel setup data digest: sha2-256:{}", hex::encode(setup_data_sha2_256_digest));
    log::debug!("Kernel command-line: {}", kernel_cmdline);
    log::debug!("Initial RAM disk digest: sha2-256:{}", hex::encode(ram_disk_sha2_256_digest));
    log::debug!("ACPI table generation digest: sha2-256:{}", hex::encode(acpi_sha2_256_digest));
    log::debug!("E820 table digest: sha2-256:{}", hex::encode(memory_map_sha2_256_digest));
    log::debug!("Event digest: sha2-256:{}", hex::encode(event_sha2_256_digest));
    log::debug!(
        "Transparent event digest: sha2-256:{}",
        hex::encode(transparent_event_sha2_256_digest)
    );

    let mut attester = P::get_attester().expect("couldn't get a valid attester");
    attester
        .extend_transparent(&stage0_event[..], &stage0_transparent_event[..])
        .expect("couldn't extend attester");
    let mut serialized_attestation_data = attester.serialize();

    let mut attestation_data: DiceData =
        try_decode_length_delimited_proto(&serialized_attestation_data[..])
            .expect("couldn't decode attestation data");

    let mut attestation_data_struct =
        oak_stage0_dice::dice_data_proto_to_stage0_dice_data(&attestation_data)
            .expect("couldn't create attestation data struct");

    // Zero out the copy of the private key in the proto that we just created if it
    // exists.
    if let Some(certificate_authority) = attestation_data.certificate_authority.as_mut() {
        certificate_authority.eca_private_key.zeroize()
    };

    attestation_data_struct.layer_1_cdi.cdi[..].copy_from_slice(&cdi[..]);
    // Zero out the copy of the sealing CDIs.
    cdi.zeroize();

    let attestation_data = Box::leak(Box::new_in(attestation_data_struct, &crate::BOOT_ALLOC));

    // Reserve the memory containing the DICE data.
    zero_page.insert_e820_entry(BootE820Entry::new(
        attestation_data.as_bytes().as_ptr() as usize,
        attestation_data.as_bytes().len(),
        E820EntryType::RESERVED,
    ));
    let mut sensitive_attestation_data_length =
        core::mem::size_of::<oak_dice::evidence::Stage0DiceData>();

    // Write Eventlog data to memory.
    let mut event_log = Vec::with_capacity_in(PAGE_SIZE, &crate::BOOT_ALLOC);
    // Ensure that Eventlog is not too big. The 8 bytes are reserved for the size of
    // the encoded eventlog proto.
    let serialized_event_log = encode_length_delimited_proto(&event_log_proto);
    assert!(serialized_event_log.len() < PAGE_SIZE);
    // First copy the size of the encoded proto in Little Endian format. Then copy
    // the actual EventLog.
    event_log.extend_from_slice(serialized_event_log.as_bytes());
    let event_log_data = event_log.leak();
    // Reserve memory containing Eventlog Data.
    zero_page.insert_e820_entry(BootE820Entry::new(
        event_log_data.as_bytes().as_ptr() as usize,
        PAGE_SIZE,
        E820EntryType::RESERVED,
    ));

    sensitive_attestation_data_length += PAGE_SIZE;

    // TODO: b/360223468 - Combine the DiceData proto with the EventLog Proto and
    // write all of it in memory.
    // Write DiceData protobuf bytes to memory.
    let mut encoded_attestation_proto = Vec::with_capacity_in(DOUBLE_PAGE_SIZE, &crate::BOOT_ALLOC);
    // Ensure that DiceData proto bytes is not too big. The 8 bytes are reserved for
    // the size of the encoded DiceData proto.
    assert!(
        serialized_attestation_data.len()
            < DOUBLE_PAGE_SIZE - size_of_val(&STAGE0_DICE_PROTO_MAGIC)
    );
    // Insert a magic number to ensure the correctness of the data being read.
    encoded_attestation_proto.extend_from_slice(STAGE0_DICE_PROTO_MAGIC.to_le_bytes().as_slice());
    encoded_attestation_proto.extend_from_slice(serialized_attestation_data.as_ref());
    // Zero out the serialized proto since it contains a copy of the private key.
    serialized_attestation_data.zeroize();

    let encoded_attestation_proto_data = encoded_attestation_proto.leak();

    // Reserve memory containing DICE proto Data.
    zero_page.insert_e820_entry(BootE820Entry::new(
        encoded_attestation_proto_data.as_bytes().as_ptr() as usize,
        DOUBLE_PAGE_SIZE,
        E820EntryType::RESERVED,
    ));
    sensitive_attestation_data_length += DOUBLE_PAGE_SIZE;

    // Append the DICE data address to the kernel command-line.
    // TODO: b/463325402 - Remove eventlog and dice data from kernel command-line
    // and only use the new DICE_DATA_ATTESTATION_PARAM arg with the serialized
    // attester.
    let extra = format!(
        "--{DICE_DATA_CMDLINE_PARAM}={attestation_data:p} --{EVENTLOG_CMDLINE_PARAM}={event_log_data:p} --{DICE_DATA_LENGTH_CMDLINE_PARAM}={sensitive_attestation_data_length}"
    );
    let extra = if cfg!(feature = "cmdline_with_serialized_attestation_data") {
        format!("{extra} --{DICE_DATA_ATTESTATION_PARAM}={encoded_attestation_proto_data:p}")
    } else {
        extra
    };

    let cmdline = if kernel_cmdline.is_empty() {
        extra
    } else if kernel_cmdline.contains("--") {
        format!("{} {}", kernel_cmdline, extra)
    } else {
        format!("{} -- {}", kernel_cmdline, extra)
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

impl<T: zerocopy::IntoBytes + zerocopy::Immutable + ?Sized> Measured for T {
    fn measure(&self) -> Measurement {
        let mut measurement = Measurement::default();
        let mut digest = Sha256::default();
        digest.update(self.as_bytes());
        let digest = digest.finalize();
        measurement[..].copy_from_slice(&digest[..]);
        measurement
    }
}
