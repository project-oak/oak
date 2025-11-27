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
use uart_16550::SerialPort;

pub struct Serial {
    port: AtomicRefCell<SerialPort>,
}

// Base I/O port for the second serial port in the system (colloquially known as
// COM2)
static COM2_BASE: u16 = 0x2f8;

impl Serial {
    pub fn new() -> Serial {
        // Our contract with the loader requires the second serial port to be
        // available, so assuming the loader adheres to it, this is safe.
        let mut port = unsafe { SerialPort::new(COM2_BASE) };
        port.init();
        Serial { port: AtomicRefCell::new(port) }
    }
}

impl oak_channel::Write for Serial {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        for byte in data {
            self.port.borrow_mut().send_raw(*byte);
        }
        Ok(())
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        Ok(())
    }
}

impl oak_channel::Read for Serial {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        #[allow(clippy::needless_range_loop)]
        for i in 0..data.len() {
            data[i] = self.port.borrow_mut().receive();
        }
        Ok(())
    }
}
