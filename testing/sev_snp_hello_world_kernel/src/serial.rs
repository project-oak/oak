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
use sev_guest::{
    msr::{get_sev_status, SevStatus},
    serial::SerialPort as GhcbSerialPort,
};
use uart_16550::SerialPort as RawSerialPort;

extern crate log;

// Base I/O port for the first serial port in the system (colloquially known as COM1).
static COM1_BASE: u16 = 0x3f8;

/// Wrapper for the possible serial port implementations.
pub enum SerialWrapper<'a> {
    Raw(RawSerialPort),
    Ghcb(GhcbSerialPort<'a>),
}

impl Write for SerialWrapper<'_> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        match self {
            SerialWrapper::Raw(port) => port.write_str(s),
            SerialWrapper::Ghcb(port) => port.write_str(s),
        }
    }
}

lazy_static! {
    pub static ref SERIAL1: AtomicRefCell<SerialWrapper<'static>> = {
        let sev_status = get_sev_status().unwrap();
        let wrapper = if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
            let ghcb_protocol = crate::ghcb::init_ghcb(sev_status.contains(SevStatus::SNP_ACTIVE));
            // Safety: our contract with the loader requires the first serial port to be available,
            // so assuming the loader adheres to it, this is safe.
            let mut port = unsafe { GhcbSerialPort::new(COM1_BASE, ghcb_protocol) };
            port.init().expect("Couldn't initialize GHCB serial port");
            SerialWrapper::Ghcb(port)
        } else {
            // Safety: our contract with the loader requires the first serial port to be available,
            // so assuming the loader adheres to it, this is safe.
            let mut port = unsafe { RawSerialPort::new(COM1_BASE) };
            port.init();
            SerialWrapper::Raw(port)
        };

        AtomicRefCell::new(wrapper)
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
