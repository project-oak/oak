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

//! Main 'kernel' for bare-metal Oak Functions.
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

#![no_std]
#![feature(abi_x86_interrupt)]
#![feature(core_c_str)]

mod args;
mod avx;
pub mod boot;
pub mod i8042;
mod interrupts;
mod libm;
mod logging;
mod memory;
#[cfg(feature = "serial_channel")]
mod serial;

use core::panic::PanicInfo;
use log::{error, info};
use oak_remote_attestation::handshaker::{AttestationBehavior, EmptyAttestationVerifier};
use oak_remote_attestation_amd::PlaceholderAmdAttestationGenerator;
use rust_hypervisor_firmware_boot::paging;
#[cfg(not(feature = "serial_channel"))]
use rust_hypervisor_firmware_virtio::pci::VirtioPciTransport;

#[cfg(all(feature = "vsock_channel", not(feature = "serial_channel")))]
// The virtio vsock port on which to listen.
const VSOCK_PORT: u32 = 1024;

/// Main entry point for the kernel, to be called from bootloader.
pub fn start_kernel<E: boot::E820Entry, B: boot::BootInfo<E>>(info: B) -> ! {
    avx::enable_avx();
    logging::init_logging();
    interrupts::init_idt();
    paging::setup();
    // We need to be done with the boot info struct before intializing memory. For example, the
    // multiboot protocol explicitly states data can be placed anywhere in memory; therefore, it's
    // highly likely we will overwrite some data after we initialize the heap. args::init_args()
    // caches the arguments (as long they are of reasonable length) in a static variable, allowing
    // us to refer to the args in the future.
    args::init_args(info.args()).unwrap();

    let protocol = info.protocol();
    // If we don't find memory for heap, it's ok to panic.
    memory::init_allocator(info).unwrap();
    main(protocol);
}

fn main(protocol: &str) -> ! {
    info!("In main! Boot protocol:  {}", protocol);
    info!("Kernel boot args: {}", args::args());
    let attestation_behavior =
        AttestationBehavior::create(PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier);
    oak_baremetal_runtime::framing::handle_frames(get_channel(), attestation_behavior).unwrap();
}

#[cfg(feature = "serial_channel")]
fn get_channel() -> serial::Serial {
    serial::Serial::new()
}

// Use a virtio console device for the communications channel if we don't support virtio vsock.
#[cfg(all(not(feature = "vsock_channel"), not(feature = "serial_channel")))]
fn get_channel() -> virtio::console::Console<VirtioPciTransport> {
    let console = virtio::console::Console::find_and_configure_device()
        .expect("Couldn't configure PCI virtio console device.");
    info!("Console device status: {}", console.get_status());
    console
}

// Use virtio vsock for the communications channel.
#[cfg(all(feature = "vsock_channel", not(feature = "serial_channel")))]
fn get_channel() -> virtio::vsock::socket::Socket<VirtioPciTransport> {
    let vsock = virtio::vsock::VSock::find_and_configure_device()
        .expect("Couldn't configure PCI virtio vsock device.");
    info!("Socket device status: {}", vsock.get_status());
    let listener = virtio::vsock::socket::SocketListener::new(vsock, VSOCK_PORT);
    listener.accept().expect("Couldn't accept connection.")
}

/// Common panic routine for the kernel. This needs to be wrrapped in a
/// panic_handler function in individual bootloader crates.
pub fn panic(info: &PanicInfo) -> ! {
    error!("PANIC: {}", info);
    i8042::shutdown();
}
