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
//! handing the reins over to the oak_baremetal_runtime. It is in a separate crate so that we
//! could support different boot protocols (eg Linux boot protocol or PVH) that
//! require different targets, linker scripts and/or provide machine
//! information in different data structures.
//!
//! Bootloaders (and VMMs under them) have to adhere to the following protocol:
//!   * Enter 64-bit long mode, and set up basic paging -- enough to load the code, as we will set
//!     up a full page table in `start_kernel`.
//!   * Implement a `#[panic_handler]` that delegates to `panic()` in this crate.
//!   * Call `start_kernel` from the entry point of the bootloader.

#![cfg_attr(not(test), no_std)]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![feature(asm_sym)]
#![feature(naked_functions)]
#![feature(once_cell)]

mod args;
mod avx;
mod descriptors;
mod elf;
mod ghcb;
pub mod i8042;
#[cfg(feature = "c_interface")]
mod interface;
mod interrupts;
mod libm;
mod logging;
mod memory;
mod mm;
#[cfg(feature = "serial_channel")]
mod serial;
#[cfg(feature = "simple_io_channel")]
mod simpleio;
#[cfg(any(feature = "virtio_console_channel", feature = "vsock_channel"))]
mod virtio;

extern crate alloc;

use crate::mm::Translator;
use alloc::{alloc::Allocator, boxed::Box};
use core::{cell::OnceCell, marker::Sync, panic::PanicInfo, str::FromStr};
use linked_list_allocator::LockedHeap;
use log::{error, info};
use oak_channel::Channel;
use oak_linux_boot_params::BootParams;
use sev_guest::msr::{get_sev_status, SevStatus};
use strum::{EnumIter, EnumString, IntoEnumIterator};
use x86_64::{
    structures::paging::{Page, Size2MiB},
    VirtAddr,
};

static mut GUEST_HOST_HEAP: OnceCell<LockedHeap> = OnceCell::new();

/// Main entry point for the kernel, to be called from bootloader.
pub fn start_kernel(info: &BootParams) -> Box<dyn Channel> {
    avx::enable_avx();
    descriptors::init_gdt();
    interrupts::init_idt();
    let sev_status = get_sev_status().unwrap_or(SevStatus::empty());
    logging::init_logging();

    // We need to be done with the boot info struct before intializing memory. For example, the
    // multiboot protocol explicitly states data can be placed anywhere in memory; therefore, it's
    // highly likely we will overwrite some data after we initialize the heap. args::init_args()
    // caches the arguments (as long they are of reasonable length) in a static variable, allowing
    // us to refer to the args in the future.
    let kernel_args = args::init_args(info.args()).unwrap();
    info!("Kernel boot args: {}", kernel_args.args());

    let protocol = info.protocol();
    info!("Boot protocol:  {}", protocol);

    // Safety: in the linker script we specify that the ELF header should be placed at 0x200000.
    let program_headers = unsafe { elf::get_phdrs(VirtAddr::new(0x20_0000)) };

    // Physical frame allocator: support up to 128 GiB of memory, for now.
    let mut frame_allocator = mm::init::<1024>(info.e820_table(), program_headers);

    let mut mapper = mm::init_paging(&mut frame_allocator, program_headers).unwrap();

    // Now that the page tables have been updated, we have to re-share the GHCB with the hypervisor.
    ghcb::reshare_ghcb(&mut mapper);

    // Allocate a section for guest-host communication (without the `ENCRYPTED` bit set)
    // We'll allocate 2*2MiB, as virtio needs more than 2 MiB for its data structures.
    let guest_host_frames = frame_allocator.allocate_contiguous(2).unwrap();
    let guest_host_pages = Page::range(
        mapper
            .translate_physical_frame(guest_host_frames.start)
            .unwrap(),
        mapper
            .translate_physical_frame(guest_host_frames.end)
            .unwrap(),
    );

    // Safety: initializing the new heap is safe as the frame allocator guarantees we're not
    // overwriting any other memory; writing to the static mut is safe as we're in the
    // initialization code and thus there can be no concurrent access.
    let guest_host_heap = unsafe {
        GUEST_HOST_HEAP
            .get_or_init(|| memory::init_guest_host_heap(guest_host_pages, &mut mapper).unwrap())
    };

    // If we don't find memory for heap, it's ok to panic.
    let heap_phys_frames = frame_allocator.largest_available().unwrap();
    memory::init_kernel_heap::<Size2MiB>(Page::range(
        mapper
            .translate_physical_frame(heap_phys_frames.start)
            .unwrap(),
        mapper
            .translate_physical_frame(heap_phys_frames.end + 1)
            .unwrap(),
    ))
    .unwrap();

    get_channel(&kernel_args, &mapper, guest_host_heap, sev_status)
}

#[derive(EnumIter, EnumString)]
#[strum(ascii_case_insensitive, serialize_all = "snake_case")]
enum ChannelType {
    #[cfg(feature = "virtio_console_channel")]
    VirtioConsole,
    #[cfg(feature = "vsock_channel")]
    VirtioVsock,
    #[cfg(feature = "serial_channel")]
    Serial,
    #[cfg(feature = "simple_io_channel")]
    SimpleIo,
}

/// Create a channel for communicating with the Untrusted Launcher.
fn get_channel<'a, X: Translator, A: Allocator + Sync>(
    kernel_args: &args::Args,
    mapper: &X,
    alloc: &'a A,
    sev_status: SevStatus,
) -> Box<dyn Channel + 'a> {
    // If we weren't told which channel to use, arbitrarily pick the first one in the `ChannelType`
    // enum. Depending on features that are enabled, this means that the enum acts as kind of a
    // reverse priority list for defaults.
    let chan_type = kernel_args
        .get("channel")
        .map(|chan_type| ChannelType::from_str(chan_type).unwrap())
        .unwrap_or_else(|| ChannelType::iter().next().unwrap());

    match chan_type {
        #[cfg(feature = "virtio_console_channel")]
        ChannelType::VirtioConsole => Box::new(virtio::get_console_channel(mapper, alloc)),
        #[cfg(feature = "vsock_channel")]
        ChannelType::VirtioVsock => Box::new(virtio::get_vsock_channel(mapper, alloc)),
        #[cfg(feature = "serial_channel")]
        ChannelType::Serial => Box::new(serial::Serial::new()),
        #[cfg(feature = "simple_io_channel")]
        ChannelType::SimpleIo => {
            Box::new(simpleio::SimpleIoChannel::new(mapper, alloc, sev_status))
        }
    }
}

/// Common panic routine for the kernel. This needs to be wrapped in a
/// panic_handler function in individual bootloader crates.
pub fn panic(info: &PanicInfo) -> ! {
    error!("PANIC: {}", info);
    i8042::shutdown();
}
