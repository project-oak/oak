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

use core::{fmt::Write, ops::DerefMut};

use log::info;
use oak_hal::{Port, PortFactory};
use spinning_top::Spinlock;

extern crate log;

// Base I/O port for the first serial port in the system (colloquially known as
// COM1)
const COM1_BASE: u16 = 0x3f8;

type SerialPort = sev_serial::SerialPort<PortFactory, Port<u8>, Port<u8>>;
pub static SERIAL1: Spinlock<Option<SerialPort>> = Spinlock::new(None);

struct Logger {}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        let mut lock = SERIAL1.lock();
        // Don't log anything if the port is not initialized yet.
        if let Some(port) = lock.deref_mut() {
            writeln!(port, "kernel {}: {}", record.level(), record.args()).unwrap();
        }
    }

    fn flush(&self) {
        // No-op, as we can't flush the serial port.
    }
}

static LOGGER: Logger = Logger {};

pub fn init_logging<P: crate::Platform>() {
    // Our contract with the launcher requires the first serial port to be
    // available, so assuming the loader adheres to it, this is safe.
    let mut port = unsafe { SerialPort::new(COM1_BASE, P::port_factory()) };
    port.init().expect("couldn't initialize logging serial port");
    {
        let mut lock = SERIAL1.lock();
        *lock.deref_mut() = Some(port);
    }
    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Debug);
    // Log a message to ensure the serial logging channel is intialized.
    info!("Logging initialised.");
}
