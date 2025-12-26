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

use oak_sev_guest::io::{PortFactoryWrapper, PortWrapper};
use spinning_top::Spinlock;

type SerialPort = sev_serial::SerialPort<PortFactoryWrapper, PortWrapper<u8>, PortWrapper<u8>>;

pub struct Serial {
    port: Spinlock<SerialPort>,
}

// Base I/O port for the second serial port in the system (colloquially known as
// COM2)
static COM2_BASE: u16 = 0x2f8;

impl Serial {
    pub fn new(sev_es_enabled: bool) -> Serial {
        let port_factory = if sev_es_enabled {
            crate::ghcb::get_ghcb_port_factory()
        } else {
            PortFactoryWrapper::new_raw()
        };
        // Our contract with the launcher requires the second serial port to be
        // available when using a serial channel for communication, so assuming the
        // loader adheres to it, this is safe.
        let mut port = unsafe { SerialPort::new(COM2_BASE, port_factory) };
        port.init().expect("couldn't initialize comms serial port");
        Serial { port: Spinlock::new(port) }
    }
}

impl oak_channel::Write for Serial {
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        let mut port = self.port.lock();
        for byte in data {
            port.send(*byte).map_err(anyhow::Error::msg)?;
        }
        Ok(())
    }

    fn flush(&mut self) -> anyhow::Result<()> {
        Ok(())
    }
}

impl oak_channel::Read for Serial {
    fn read_exact(&mut self, data: &mut [u8]) -> anyhow::Result<()> {
        let mut port = self.port.lock();
        #[allow(clippy::needless_range_loop)]
        for i in 0..data.len() {
            data[i] = port.receive().map_err(anyhow::Error::msg)?;
        }
        Ok(())
    }
}
