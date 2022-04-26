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

impl Serial {
    pub fn new() -> Serial {
        let mut port = unsafe { SerialPort::new(0x2f8) };
        port.init();
        Serial {
            port: AtomicRefCell::new(port),
        }
    }
}

impl runtime::Channel for Serial {
    type Error = ();

    fn send(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        for byte in data {
            self.port.borrow_mut().send(*byte);
        }
        Ok(())
    }

    fn recv(&mut self, data: &mut [u8]) -> Result<(), Self::Error> {
        #[allow(clippy::needless_range_loop)]
        for i in 0..data.len() {
            data[i] = self.port.borrow_mut().receive();
        }
        Ok(())
    }
}
