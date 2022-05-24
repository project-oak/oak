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
//! handing the reins over to the runtime. It is in a separate crate so that we
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

mod avx;
pub mod boot;
pub mod i8042;
mod interrupts;
mod libm;
mod logging;
mod memory;
mod serial;

use core::panic::PanicInfo;
use log::{error, info};
use rust_hypervisor_firmware_subset::paging;

/// Main entry point for the kernel, to be called from bootloader.
pub fn start_kernel<E: boot::E820Entry, B: boot::BootInfo<E>>(info: &B) -> ! {
    avx::enable_avx();
    logging::init_logging();
    interrupts::init_idt();
    paging::setup();
    // If we don't find memory for heap, it's ok to panic.
    memory::init_allocator(info.e820_table()).unwrap();
    main(info);
}

fn main<E: boot::E820Entry, B: boot::BootInfo<E>>(info: &B) -> ! {
    info!("In main! Boot protocol:  {}", info.protocol());
    let serial = serial::Serial::new();
    runtime::framing::handle_frames(serial).unwrap();
}

/// Common panic routine for the kernel. This needs to be wrrapped in a
/// panic_handler function in individual bootloader crates.
pub fn panic(info: &PanicInfo) -> ! {
    error!("PANIC: {}", info);
    i8042::shutdown();
}
