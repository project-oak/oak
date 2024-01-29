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

use sev_serial::SerialPort;
use spinning_top::Spinlock;

use crate::io_port_factory;

extern crate log;

// Base I/O port for the first serial port in the system (colloquially known as COM1)
static SERIAL_BASE: u16 = 0x3f8;
static SERIAL_PORT: Spinlock<Option<SerialPort>> = Spinlock::new(None);

struct Logger {}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        let mut lock = SERIAL_PORT.lock();
        // Don't log anything if the port is not initialized yet.
        if let Some(port) = lock.deref_mut() {
            writeln!(port, "stage0 {}: {}", record.level(), record.args()).unwrap();
        }
    }

    fn flush(&self) {
        // No-op, as we can't flush the serial port.
    }
}

static LOGGER: Logger = Logger {};

pub fn init_logging() {
    // Our contract with the launcher requires the first serial port to be
    // available, so assuming the loader adheres to it, this is safe.
    let mut port = unsafe { SerialPort::new(SERIAL_BASE, io_port_factory()) };
    port.init()
        .expect("couldn't initialize logging serial port");
    {
        let mut lock = SERIAL_PORT.lock();
        *lock.deref_mut() = Some(port);
    }
    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Debug);
}
