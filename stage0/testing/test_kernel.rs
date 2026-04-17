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

#![no_std]
#![no_main]

use core::{cell::OnceCell, fmt::Write, panic::PanicInfo};

use oak_linux_boot_params::BootParams;
use spinning_top::Spinlock;
use uart_16550::SerialPort;
use x86_64::instructions::{hlt, interrupts::int3};

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

    writeln!(serial.get_mut().unwrap(), "boot successful").unwrap();
    abort();
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("{}", info);
    abort();
}

fn abort() -> ! {
    // Trigger a breakpoint exception. As we don't have a #BP handler, this will
    // triple fault and terminate the program.
    int3();

    loop {
        hlt();
    }
}
