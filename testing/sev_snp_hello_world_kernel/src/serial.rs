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
use lazy_static::lazy_static;
use sev_guest::{
    ghcb::{Ghcb, GhcbProtocol},
    io::{GhcbIoFactory, RawIoPortFactory},
    msr::{get_sev_status, SevStatus},
};
use sev_serial::{RawSerialPort, StaticGhcbSerialPort};
use spinning_top::{RawSpinlock, Spinlock};

extern crate log;

// Base I/O port for the first serial port in the system (colloquially known as COM1).
static COM1_BASE: u16 = 0x3f8;

/// Wrapper for the possible serial port implementations.
pub enum SerialWrapper<'a> {
    Raw(RawSerialPort<'a>),
    Ghcb(StaticGhcbSerialPort<RawSpinlock>),
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
    static ref GHCB_PROTOCOL: Spinlock<GhcbProtocol<'static, Ghcb>> = {
        let sev_status = get_sev_status().unwrap_or(SevStatus::empty());
        Spinlock::new(crate::ghcb::init_ghcb(
            sev_status.contains(SevStatus::SNP_ACTIVE),
        ))
    };
}

lazy_static! {
    pub static ref SERIAL1: Spinlock<SerialWrapper<'static>> = {
        let sev_status = get_sev_status().unwrap_or(SevStatus::empty());
        let wrapper = if sev_status.contains(SevStatus::SEV_ES_ENABLED) {
            let ghcb_factory = GhcbIoFactory::new(&GHCB_PROTOCOL);
            // Safety: our contract with the loader requires the first serial port to be available,
            // so assuming the loader adheres to it, this is safe.
            let mut port = unsafe { StaticGhcbSerialPort::new(COM1_BASE, ghcb_factory) };
            port.init().expect("Couldn't initialize GHCB serial port");
            SerialWrapper::Ghcb(port)
        } else {
            // Safety: our contract with the loader requires the first serial port to be available,
            // so assuming the loader adheres to it, this is safe.
            let mut port = unsafe { RawSerialPort::new(COM1_BASE, RawIoPortFactory) };
            port.init().expect("Couldn't initialize raw serial port");
            SerialWrapper::Raw(port)
        };

        Spinlock::new(wrapper)
    };
}

struct Logger {}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        writeln!(SERIAL1.lock(), "{}: {}", record.level(), record.args()).unwrap();
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
