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

use core::fmt::Write;
use log::info;
use oak_sev_guest::io::PortFactoryWrapper;
use sev_serial::SerialPort;
use spinning_top::Spinlock;

extern crate log;

// Base I/O port for the first serial port in the system (colloquially known as COM1)
const COM1_BASE: u16 = 0x3f8;

pub static SERIAL1: Spinlock<Option<SerialPort>> = Spinlock::new(None);

struct Logger {}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        writeln!(
            SERIAL1.lock().as_mut().unwrap(),
            "kernel {}: {}",
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

pub fn init_logging(sev_es_enabled: bool) {
    let port_factory = if sev_es_enabled {
        crate::ghcb::get_ghcb_port_factory()
    } else {
        PortFactoryWrapper::new_raw()
    };
    // Our contract with the launcher requires the first serial port to be
    // available, so assuming the loader adheres to it, this is safe.
    let mut port = unsafe { SerialPort::new(COM1_BASE, port_factory) };
    port.init()
        .expect("couldn't initialize logging serial port");

    if SERIAL1.lock().replace(port).is_some() {
        panic!("serial port 1 is already initialized");
    }

    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Debug);
    // Log a message to ensure the serial logging channel is intialized.
    info!("Logging initialised.");
}
