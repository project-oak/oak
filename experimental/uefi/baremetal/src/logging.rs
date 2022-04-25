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
use uart_16550::SerialPort;

extern crate log;

struct Logger {
    port: AtomicRefCell<SerialPort>,
}

impl Logger {
    pub unsafe fn new() -> Self {
        let mut port = SerialPort::new(0x3f8);
        port.init();
        Logger {
            port: AtomicRefCell::new(port),
        }
    }
}

impl log::Log for Logger {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        writeln!(
            self.port.borrow_mut(),
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

static mut LOGGER: Option<Logger> = None;

pub unsafe fn init_logging() {
    LOGGER = Some(Logger::new());
    log::set_logger(LOGGER.as_ref().unwrap()).unwrap();
    log::set_max_level(log::LevelFilter::Info);
}
