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
#![feature(asm_sym)]
#![feature(naked_functions)]
#![feature(once_cell)]

mod args;
mod avx;
mod descriptors;
mod elf;
pub mod i8042;
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

use alloc::boxed::Box;
use core::{panic::PanicInfo, str::FromStr};
use log::{error, info};
use oak_channel::Channel;
use oak_linux_boot_params::BootParams;
use strum::{EnumIter, EnumString, IntoEnumIterator};
use x86_64::{
    structures::paging::{Page, Size2MiB},
    VirtAddr,
};

use crate::mm::Translate;

/// Main entry point for the kernel, to be called from bootloader.
pub fn start_kernel(info: &BootParams) -> Box<dyn Channel> {
    avx::enable_avx();
    logging::init_logging();
    descriptors::init_gdt();
    interrupts::init_idt();

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

    let mapper = mm::init_paging(&mut frame_allocator, program_headers).unwrap();

    // If we don't find memory for heap, it's ok to panic.
    let heap_phys_frames = frame_allocator.largest_available().unwrap();
    memory::init_allocator::<Size2MiB>(Page::range(
        mapper.translate_frame(heap_phys_frames.start).unwrap(),
        mapper.translate_frame(heap_phys_frames.end + 1).unwrap(),
    ))
    .unwrap();

    get_channel(&kernel_args, &mapper)
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
fn get_channel<A: Translate>(kernel_args: &args::Args, mapper: &A) -> Box<dyn Channel> {
    // If we weren't told which channel to use, arbitrarily pick the first one in the `ChannelType`
    // enum. Depending on features that are enabled, this means that the enum acts as kind of a
    // reverse priority list for defaults.
    let chan_type = kernel_args
        .get("channel")
        .map(|chan_type| ChannelType::from_str(chan_type).unwrap())
        .unwrap_or_else(|| ChannelType::iter().next().unwrap());

    match chan_type {
        #[cfg(feature = "virtio_console_channel")]
        ChannelType::VirtioConsole => Box::new(virtio::get_console_channel(mapper)),
        #[cfg(feature = "vsock_channel")]
        ChannelType::VirtioVsock => Box::new(virtio::get_vsock_channel(mapper)),
        #[cfg(feature = "serial_channel")]
        ChannelType::Serial => Box::new(serial::Serial::new()),
        #[cfg(feature = "simple_io_channel")]
        ChannelType::SimpleIo => Box::new(simpleio::SimpleIoChannel::new(mapper)),
    }
}

/// Common panic routine for the kernel. This needs to be wrapped in a
/// panic_handler function in individual bootloader crates.
pub fn panic(info: &PanicInfo) -> ! {
    error!("PANIC: {}", info);
    i8042::shutdown();
}
