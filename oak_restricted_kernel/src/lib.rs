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

//! Main 'kernel' for baremetal Oak Functions.
//!
//! This code takes care of initializing the x86-64 machine properly and
//! handing the reins over to the oak_baremetal_runtime. It is in a separate
//! crate so that we could support different boot protocols (eg Linux boot
//! protocol or PVH) that require different targets, linker scripts and/or
//! provide machine information in different data structures.
//!
//! Bootloaders (and VMMs under them) have to adhere to the following protocol:
//!   * Enter 64-bit long mode, and set up basic paging -- enough to load the
//!     code, as we will set up a full page table in `start_kernel`.
//!   * Implement a `#[panic_handler]` that delegates to `panic()` in this
//!     crate.
//!   * Call `start_kernel` from the entry point of the bootloader.

#![no_std]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![feature(array_chunks)]
#![feature(naked_functions)]
#![feature(c_size_t)]
#![feature(never_type)]

mod acpi;
mod args;
mod avx;
mod descriptors;
mod elf;
mod ghcb;
mod interrupts;
mod libm;
mod logging;
mod memory;
mod mm;
mod processes;
#[cfg(feature = "serial_channel")]
mod serial;
pub mod shutdown;
#[cfg(feature = "simple_io_channel")]
mod simpleio;
mod snp;
mod syscall;
#[cfg(feature = "virtio_console_channel")]
mod virtio_console;

#[cfg(test)]
extern crate std;

extern crate alloc;

use alloc::{alloc::Allocator, boxed::Box, vec::Vec};
use core::{panic::PanicInfo, pin::Pin, str::FromStr};

use linked_list_allocator::LockedHeap;
use log::{error, info};
use mm::{
    frame_allocator::PhysicalMemoryAllocator, page_tables::CurrentRootPageTable,
    virtual_address_allocator::VirtualAddressAllocator,
};
use oak_channel::Channel;
use oak_core::sync::OnceCell;
use oak_linux_boot_params::BootParams;
use oak_sev_guest::msr::{change_snp_state_for_frame, get_sev_status, PageAssignment, SevStatus};
use spinning_top::Spinlock;
use strum::{EnumIter, EnumString, IntoEnumIterator};
use x86_64::{
    structures::paging::{Page, PageTable, Size2MiB},
    PhysAddr, VirtAddr,
};
use zerocopy::FromBytes;
use zeroize::Zeroize;

use crate::{
    acpi::Acpi,
    mm::Translator,
    processes::Process,
    snp::{get_snp_page_addresses, init_snp_pages},
};

/// Allocator for physical memory frames in the system.
/// We reserve enough room to handle up to 512 GiB of memory, for now.
pub static FRAME_ALLOCATOR: Spinlock<PhysicalMemoryAllocator<4096>> =
    Spinlock::new(PhysicalMemoryAllocator::new());

/// The allocator for allocating space in the memory area that is shared with
/// the hypervisor.
pub static GUEST_HOST_HEAP: OnceCell<LockedHeap> = OnceCell::new();

/// Active page tables.
pub static PAGE_TABLES: Spinlock<CurrentRootPageTable> =
    Spinlock::new(CurrentRootPageTable::empty());

/// Level 4 page table that is free in application space, but has all entries
/// for kernel space populated. It can be used to create free page tables for
/// applications, that maintain correct mapping in kernel space.
pub static BASE_L4_PAGE_TABLE: OnceCell<Pin<Box<PageTable>>> = OnceCell::new();

/// Allocator for long-lived pages in the kernel.
pub static VMA_ALLOCATOR: Spinlock<VirtualAddressAllocator<Size2MiB>> =
    Spinlock::new(VirtualAddressAllocator::new(Page::range(
        // Assign 32 TB of virtual memory for this allocator.
        // Safety: these addresses are constants and thus we know they're page-aligned.
        unsafe {
            Page::from_start_address_unchecked(VirtAddr::new_truncate(0xFFFF_C900_0000_0000))
        },
        unsafe {
            Page::from_start_address_unchecked(VirtAddr::new_truncate(0xFFFF_E900_0000_0000))
        },
    )));

/// Main entry point for the kernel, to be called from bootloader.
pub fn start_kernel(info: &BootParams) -> ! {
    avx::enable_avx();
    descriptors::init_gdt_early();
    interrupts::init_idt_early();
    let sev_status = get_sev_status().unwrap_or(SevStatus::empty());
    let sev_es_enabled = sev_status.contains(SevStatus::SEV_ES_ENABLED);
    let sev_snp_enabled = sev_status.contains(SevStatus::SNP_ACTIVE);
    if sev_es_enabled {
        ghcb::init(sev_snp_enabled);
    }
    logging::init_logging(sev_es_enabled);

    // Safety: we shouldn't have anything else but the PICs on the I/O ports.
    // If we get an error, we will still try to continue.
    if let Err(err) = unsafe { interrupts::init_pic8259(sev_status) } {
        log::warn!("error disabling 8259 PIC: {}", err);
    }

    // We need to be done with the boot info struct before intializing memory. For
    // example, the multiboot protocol explicitly states data can be placed
    // anywhere in memory; therefore, it's highly likely we will overwrite some
    // data after we initialize the heap. args::init_args() caches the arguments
    // (as long they are of reasonable length) in a static variable, allowing us
    // to refer to the args in the future.
    let kernel_args = args::init_args(info.args()).unwrap();
    info!("Kernel boot args: {}", kernel_args.args());

    let protocol = info.protocol();
    info!("Boot protocol:  {}", protocol);
    let snp_pages = if sev_snp_enabled {
        // We have to get the physical addresses of the CPUID pages now while the
        // identity mapping is still in place, but we can only initialize the
        // instances after the new page mappings have been set up.
        Some(get_snp_page_addresses(info))
    } else {
        None
    };

    // Safety: in the linker script we specify that the ELF header should be placed
    // at 0x200000.
    let program_headers = unsafe { elf::get_phdrs(VirtAddr::new(0x20_0000)) };

    let ramdisk = info.ramdisk().expect("expected to find a ramdisk");

    // Physical frame allocator
    mm::init(info.e820_table(), program_headers, &ramdisk);

    // Note: `info` will not be valid after calling this!
    {
        let pml4_frame = mm::initial_pml4(program_headers).unwrap();
        // Prevent execution code in data only memory pages.
        // Safety: executeable memory is assumed to be appropiately marked in the page
        // table.
        unsafe {
            x86_64::registers::model_specific::Efer::update(|flags| {
                flags.insert(x86_64::registers::model_specific::EferFlags::NO_EXECUTE_ENABLE)
            });
        };
        // Safety: the new page tables keep the identity mapping at -2GB intact, so it's
        // safe to load the new page tables.
        let prev_page_table = unsafe { PAGE_TABLES.lock().replace(pml4_frame) };
        assert!(
            prev_page_table.is_none(),
            "there should be no previous page table during initialization"
        );

        // Safety: We just created a page table at this location on the heap.
        let pml4: PageTable = unsafe {
            *Box::from_raw(
                (PAGE_TABLES
                    .lock()
                    .get()
                    .unwrap()
                    .translate_physical(PhysAddr::new(pml4_frame.start_address().as_u64()))
                    .expect("page table must map to virtual address"))
                // Safety: We get a mut pointer here to satisfy the type system. However, the pml4
                // will not be mutated. This is since while using this pml4 the kernel will not
                // allocate memory in application space, and since all the kernel space entries of
                // this pml4 are already populated with existing pointers to pml3 page tables. Only
                // those pml3 tables will be modified when allocating kernel space memory.
                .as_mut_ptr(),
            )
        };
        BASE_L4_PAGE_TABLE.set(Box::pin(pml4)).expect("base pml4 not unset");
    };

    // Re-map boot params to the new virtual address.
    // Safety: we know we're addressing valid memory that contains the correct data
    // structure, as we're just translating addresses differently due to the new
    // page tables.
    let info = unsafe {
        #[allow(clippy::unnecessary_cast)]
        (PAGE_TABLES
            .lock()
            .get()
            .unwrap()
            .translate_physical(PhysAddr::new(info as *const _ as u64))
            .unwrap()
            .as_ptr() as *const BootParams)
            .as_ref()
            .unwrap()
    };

    if sev_es_enabled {
        let pt_guard = PAGE_TABLES.lock();
        let mapper = pt_guard.get().unwrap();
        // Now that the page tables have been updated, we have to re-share the GHCB with
        // the hypervisor.
        ghcb::reshare_ghcb(mapper);
        if sev_snp_enabled {
            // We must also initialise the CPUID and secrets pages and the guest message
            // encryptor when SEV-SNP is active. Panicking is OK at this point,
            // because these pages are required to support the full features and
            // we don't want to run without them.
            init_snp_pages(snp_pages.expect("missing SNP CPUID and secrets pages"), mapper);
        }
    }

    // Allocate a section for guest-host communication (without the `ENCRYPTED` bit
    // set) We'll allocate 2*2MiB, as virtio needs more than 2 MiB for its data
    // structures.
    let guest_host_frames = FRAME_ALLOCATOR.lock().allocate_contiguous(2).unwrap();

    let guest_host_pages = {
        let pt_guard = PAGE_TABLES.lock();
        let pt = pt_guard.get().unwrap();
        Page::range(
            pt.translate_physical_frame(guest_host_frames.start).unwrap(),
            pt.translate_physical_frame(guest_host_frames.end).unwrap(),
        )
    };

    // If we are running on SNP we have to mark the guest-host frames as shared in
    // the RMP. It is OK to crash if we cannot mark the pages as shared in the
    // RMP.
    if sev_snp_enabled {
        // TODO(#3414): Use the GHCB protocol when it is available.
        for frame in guest_host_frames {
            change_snp_state_for_frame(&frame, PageAssignment::Shared)
                .expect("couldn't change SNP state for frame");
        }
    }

    // Safety: initializing the new heap is safe as the frame allocator guarantees
    // we're not overwriting any other memory; writing to the static mut is safe
    // as we're in the initialization code and thus there can be no concurrent
    // access.
    if GUEST_HOST_HEAP
        .set(
            unsafe {
                memory::init_guest_host_heap(guest_host_pages, PAGE_TABLES.lock().get().unwrap())
            }
            .unwrap(),
        )
        .is_err()
    {
        panic!("couldn't initialize the guest-host heap");
    }

    // If we don't find memory for heap, it's ok to panic.
    // We'll let the heap to grow to 1 TB (1 << 19 * 2 MiB pages), max.
    let heap_page_range = VMA_ALLOCATOR.lock().allocate(1 << 19).unwrap();
    memory::init_kernel_heap(heap_page_range).unwrap();

    struct SensitiveDiceDataMemory {
        start_ptr: *mut u8,
        eventlog_ptr: *mut u8,
        sensitive_memory_length: usize,
    }

    impl SensitiveDiceDataMemory {
        /// Safety: Caller must ensure that there is only instance of this
        /// struct.
        unsafe fn new(kernel_args: &args::Args, info: &oak_linux_boot_params::BootParams) -> Self {
            let sensitive_memory_length = kernel_args
                .get(&alloc::format!("--{}", oak_dice::evidence::DICE_DATA_LENGTH_CMDLINE_PARAM))
                .map(|arg| {
                    arg.parse::<usize>()
                        .expect("dice data length kernel arg could not be converted to usize")
                })
                .inspect(|&length| {
                    assert!(
                        length >= core::mem::size_of::<oak_dice::evidence::Stage0DiceData>(),
                        "the cmdline argument for dice data length must be no less than the size of the Stage0DiceData struct"
                    );
                })
                // Older versions of stage0 do not supply this argument. In this case we assume the
                // lenght of the dice data is the length of the associated struct.
                .unwrap_or_else(|| core::mem::size_of::<oak_dice::evidence::Stage0DiceData>());
            let dice_data_phys_addr = {
                let arg = kernel_args
                    .get(&alloc::format!("--{}", oak_dice::evidence::DICE_DATA_CMDLINE_PARAM))
                    .expect("no dice data address supplied in the kernel args");
                let parsed_arg = u64::from_str_radix(
                    arg.strip_prefix("0x").expect("failed stripping the hex prefix"),
                    16,
                )
                .expect("couldn't parse address as a hex number");
                PhysAddr::new(parsed_arg)
            };

            let eventlog_phys_addr = {
                let arg = kernel_args
                    .get(&alloc::format!("--{}", oak_dice::evidence::EVENTLOG_CMDLINE_PARAM))
                    .expect("no eventlog address supplied in the kernel args");
                let parsed_arg = u64::from_str_radix(
                    arg.strip_prefix("0x").expect("failed stripping the hex prefix"),
                    16,
                )
                .expect("couldn't parse address as a hex number");
                PhysAddr::new(parsed_arg)
            };

            // Ensure that the dice data is stored within reserved memory.
            let end = dice_data_phys_addr + (sensitive_memory_length as u64 - 1);
            assert!(info.e820_table().iter().any(|entry| {
                let dice_data_fully_contained_in_segment = {
                    let range = PhysAddr::new(entry.addr().try_into().unwrap())
                        ..=PhysAddr::new((entry.addr() + entry.size()).try_into().unwrap());
                    range.contains(&dice_data_phys_addr)
                        && range.contains(&end)
                        && range.contains(&eventlog_phys_addr)
                };

                entry.entry_type().expect("failed to get type")
                    == oak_linux_boot_params::E820EntryType::RESERVED
                    && dice_data_fully_contained_in_segment
            }));

            let dice_data_virt_addr = {
                let pt_guard = PAGE_TABLES.lock();
                let pt = pt_guard.get().expect("failed to get page tables");
                pt.translate_physical(dice_data_phys_addr)
                    .expect("failed to translate physical dice address")
            };

            let eventlog_virt_addr = {
                let pt_guard = PAGE_TABLES.lock();
                let pt = pt_guard.get().expect("failed to get page tables");
                pt.translate_physical(eventlog_phys_addr)
                    .expect("failed to translate physical eventlog address")
            };

            Self {
                start_ptr: dice_data_virt_addr.as_mut_ptr(),
                eventlog_ptr: eventlog_virt_addr.as_mut_ptr(),
                sensitive_memory_length,
            }
        }

        fn read_stage0_dice_data(&self) -> oak_dice::evidence::Stage0DiceData {
            let dice_memory_slice = unsafe {
                core::slice::from_raw_parts(
                    self.start_ptr,
                    core::mem::size_of::<oak_dice::evidence::Stage0DiceData>(),
                )
            };

            let dice_data = oak_dice::evidence::Stage0DiceData::read_from_bytes(dice_memory_slice)
                .expect("failed to read dice data");

            if dice_data.magic != oak_dice::evidence::STAGE0_MAGIC {
                panic!("dice data loaded from stage0 failed validation");
            }
            dice_data
        }

        fn read_encoded_eventlog(&self) -> Vec<u8> {
            // Read the event log size (first 8 bytes)
            let event_log_size = unsafe {
                let size_bytes = core::slice::from_raw_parts(self.eventlog_ptr, 8);
                u64::from_le_bytes(size_bytes.try_into().unwrap()) as usize
            };

            // Read the event log bytes
            let event_log_bytes =
                unsafe { core::slice::from_raw_parts(self.eventlog_ptr.add(8), event_log_size) };

            event_log_bytes.to_vec()
        }
    }

    impl Drop for SensitiveDiceDataMemory {
        fn drop(&mut self) {
            // Zero out the sensitive_dice_data_memory.
            // Safety: This struct is only used once. We have checked the length,
            // know it is backed by physical memory and is reserved.
            (unsafe {
                core::slice::from_raw_parts_mut(self.start_ptr, self.sensitive_memory_length)
            })
            .zeroize();
        }
    }

    let (stage0_dice_data, encoded_event_log) = {
        let sensitive_dice_data =
        // Safety: This will be the only instance of this struct.
        unsafe {SensitiveDiceDataMemory::new(&kernel_args, info)};
        (sensitive_dice_data.read_stage0_dice_data(), sensitive_dice_data.read_encoded_eventlog())
    };

    // Okay. We've got page tables and a heap. Set up the "late" IDT, this time with
    // descriptors for user mode.
    let double_fault_stack = mm::allocate_stack();
    let privileged_interrupt_stack = mm::allocate_stack();
    let double_fault_stack_index =
        descriptors::init_gdt(double_fault_stack, privileged_interrupt_stack);
    // Safety: we've just loaded a new GDT with a valid IST entry for the double
    // fault.
    unsafe {
        interrupts::init_idt(double_fault_stack_index);
    }

    // Init ACPI, if the tables are available.
    let mut acpi = match acpi::Acpi::new(info) {
        Err(ref err) => {
            log::warn!("Failed to load ACPI tables: {}", err);
            None
        }
        Ok(mut acpi) => {
            acpi.print_devices().unwrap();
            Some(acpi)
        }
    };

    let channel =
        get_channel(&kernel_args, GUEST_HOST_HEAP.get().unwrap(), acpi.as_mut(), sev_status);

    let application_bytes: Box<[u8]> = {
        let virt_addr = {
            let pt_guard = PAGE_TABLES.lock();
            let pt = pt_guard.get().expect("failed to get page tables");
            pt.translate_physical(PhysAddr::new(ramdisk.addr.into()))
                .expect("failed to translate physical dice address")
        };

        // Safety:
        // We rely on the firmware to ensure this range is valid and backed by physical
        // memory.
        // We rely on the wrapper that loaded the kernel ELF file into memory, to ensure
        // it didn't over overwrite the ramdisk range.
        // We excluded this range from the frame allocator so it cannot be used by the
        // heap allocator.
        let slice: &[u8] = unsafe {
            core::slice::from_raw_parts::<u8>(
                virt_addr.as_mut_ptr(),
                info.hdr.ramdisk_size.try_into().unwrap(),
            )
        };

        info!("Copying application from ramdisk...");
        let owned_slice = Box::<[u8]>::from(slice);
        // Once the application has been copied onto the heap, the original ramdisk
        // location is marked as available.
        let ramdisk_range = crate::mm::ramdisk_range(&ramdisk);
        info!(
            "marking [{:#018x}..{:#018x}) as available",
            ramdisk_range.start.start_address().as_u64(),
            ramdisk_range.end.start_address().as_u64()
        );
        FRAME_ALLOCATOR.lock().mark_valid(ramdisk_range, true);

        owned_slice
    };

    log::info!("Binary loaded, size: {}", application_bytes.len());

    syscall::enable_syscalls(
        channel,
        syscall::dice_data::DiceData::Layer0(Box::new(stage0_dice_data)),
        encoded_event_log,
    );

    // Ensure new process is not dropped.
    // Safety: The application is assumed to be a valid ELF file.
    let process = {
        let elf_executeable =
            processes::ElfExecuteable::new(application_bytes).expect("failed to parse application");
        unsafe {
            Process::from_elf_executeable(&elf_executeable).expect("failed to create process")
        }
    };

    // Safety: syscalls have been setup, we're ready to load the app.
    unsafe {
        process
            .execute()
            .inspect_err(|err| log::error!("failed to create initial process: {:?}", err))
            .expect("failed to create initial process")
    }
}

#[derive(EnumIter, EnumString)]
#[strum(ascii_case_insensitive, serialize_all = "snake_case")]
enum ChannelType {
    #[cfg(feature = "virtio_console_channel")]
    VirtioConsole,
    #[cfg(feature = "serial_channel")]
    Serial,
    #[cfg(feature = "simple_io_channel")]
    SimpleIo,
}

/// Create a channel for communicating with the Untrusted Launcher.
#[allow(unused_variables)]
fn get_channel<'a, A: Allocator + Sync>(
    kernel_args: &args::Args,
    alloc: &'a A,
    acpi: Option<&mut Acpi>,
    sev_status: SevStatus,
) -> Box<dyn Channel + 'a> {
    // If we weren't told which channel to use, arbitrarily pick the first one in
    // the `ChannelType` enum. Depending on features that are enabled, this
    // means that the enum acts as kind of a reverse priority list for defaults.
    let chan_type = kernel_args
        .get("channel")
        .map(|chan_type| ChannelType::from_str(chan_type).unwrap())
        .unwrap_or_else(|| ChannelType::iter().next().unwrap());

    match chan_type {
        #[cfg(feature = "virtio_console_channel")]
        ChannelType::VirtioConsole => Box::new(virtio_console::get_console_channel(
            acpi.expect("ACPI not available; unable to use virtio console"),
        )),
        #[cfg(feature = "serial_channel")]
        ChannelType::Serial => {
            Box::new(serial::Serial::new(sev_status.contains(SevStatus::SEV_ES_ENABLED)))
        }
        #[cfg(feature = "simple_io_channel")]
        ChannelType::SimpleIo => Box::new(simpleio::SimpleIoChannel::new(alloc, sev_status)),
    }
}

/// Common panic routine for the kernel. This needs to be wrapped in a
/// panic_handler function in individual bootloader crates.
pub fn panic(info: &PanicInfo) -> ! {
    error!("PANIC: {}", info);
    shutdown::shutdown();
}
