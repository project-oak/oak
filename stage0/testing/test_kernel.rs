//
// Copyright 2025 The Project Oak Authors
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

//! A minimal test kernel used by the stage0 integration tests.
//!
//! After booting it prints a `boot successful` marker on the serial port. Its
//! subsequent behaviour depends on the `keep_alive` crate feature:
//!
//! * without `keep_alive` (the default): it triple-faults immediately, causing
//!   QEMU to exit. This is convenient for smoke tests that just capture the
//!   serial output and wait for the process to terminate.
//! * with `keep_alive`: it halts forever, keeping the guest alive so a test
//!   harness has a stable window to inspect guest memory (for example via the
//!   QEMU monitor `dump-guest-memory` command) once stage0 has handed control
//!   to the kernel. The harness is expected to terminate the VM when done.

#![no_std]
#![no_main]

use core::{cell::OnceCell, fmt::Write, panic::PanicInfo};

use oak_linux_boot_params::BootParams;
use spinning_top::Spinlock;
use uart_16550::SerialPort;
use x86_64::instructions::hlt;
#[cfg(not(feature = "keep_alive"))]
use x86_64::instructions::interrupts::int3;

// Base I/O port for the first serial port in the system
static SERIAL_BASE: u16 = 0x3f8;

static SERIAL_PORT: Spinlock<OnceCell<SerialPort>> = Spinlock::new(OnceCell::new());

#[unsafe(no_mangle)]
pub extern "C" fn rust64_start(_rdi: u64, _rsi: &BootParams) -> ! {
    let mut serial = SERIAL_PORT.lock();
    serial
        .set({
            let mut port = unsafe { SerialPort::new(SERIAL_BASE) };
            port.init();
            port
        })
        .unwrap();

    // Signal that stage0 has finished and handed control to the kernel. A test
    // harness may wait for this marker before inspecting the guest.
    writeln!(serial.get_mut().unwrap(), "boot successful").unwrap();
    drop(serial);

    exit();
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("{}", info);
    exit();
}

/// Terminates the guest by triple-faulting.
///
/// Triggers a breakpoint exception; as there is no `#BP` handler this escalates
/// to a triple fault, which terminates the program and makes QEMU exit.
#[cfg(not(feature = "keep_alive"))]
fn exit() -> ! {
    int3();

    loop {
        hlt();
    }
}

/// Keeps the guest alive by halting forever, so its memory can be inspected by
/// a test harness. The harness is expected to terminate the VM when done.
#[cfg(feature = "keep_alive")]
fn exit() -> ! {
    loop {
        hlt();
    }
}
