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

use atomic_refcell::AtomicRefCell;
use core::fmt::Write;
use lazy_static::lazy_static;
use sev_guest::io::PortFactoryWrapper;
use sev_serial::SerialPort;

extern crate log;

// Base I/O port for the first serial port in the system (colloquially known as COM1)
static COM1_BASE: u16 = 0x3f8;

lazy_static! {
    pub(crate) static ref SERIAL1: AtomicRefCell<SerialPort> = {
        let port_factory = PortFactoryWrapper::new_raw();
        // Our contract with the launcher requires the first serial port to be
        // available, so assuming the loader adheres to it, this is safe.
        let mut port = unsafe { SerialPort::new(COM1_BASE, port_factory) };
        port.init().expect("Couldn't initialize logging serial port.");
        AtomicRefCell::new(port)
    };
}

struct Logger {}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        writeln!(
            SERIAL1.borrow_mut(),
            "{}: {}",
            record.level(),
            record.args()
        )
        .unwrap();
    }

    fn flush(&self) {
        // No-op, as we can't flush the serial port.
    }
}

static LOGGER: Logger = Logger {};

pub fn init_logging() {
    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Debug);
}
