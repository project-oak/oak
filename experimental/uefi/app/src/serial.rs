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

use uefi::{
    prelude::*,
    proto::console::serial,
    table::boot::{OpenProtocolAttributes, OpenProtocolParams},
    Error, Handle, ResultExt, Status,
};

pub struct Serial<'boot> {
    serial: &'boot mut serial::Serial<'boot>,
}

// qemu emulates the 16550A UART controller, which has a maximum FIFO depth of 16 bytes.
const SERIAL_RECEIVE_FIFO_DEPTH: u32 = 16;

impl<'boot> Serial<'boot> {
    pub fn get(handle: Handle, bt: &BootServices, index: usize) -> Result<Serial, Error<()>> {
        // Expect (at least) two serial ports on the system; the first will be used
        // for stdio, and we can use the second one for our echo example. If we don't
        // seem to have a second serial port, err out with the (arbitrarily chosen)
        // NO_MAPPING error.
        let serial_handles = bt.find_handles::<serial::Serial>()?;
        let serial_handle = serial_handles.get(index).ok_or(Status::NO_MAPPING)?;
        let serial = bt.open_protocol::<serial::Serial>(
            OpenProtocolParams {
                handle: *serial_handle,
                agent: handle,
                controller: None,
            },
            OpenProtocolAttributes::Exclusive,
        )?;
        // Dereference the raw pointer (*mut Serial) we get to the serial interface.
        // This is safe as according to the UEFI spec for the OpenProtocol call to succeed the
        // interface must not be null (see Section 7.3 in the UEFI Specification, Version 2.9).
        let serial = unsafe { &mut *serial.interface.get() };

        // Increase the FIFO size from the default 1 byte to something bigger.
        let mut io_mode = *serial.io_mode();
        io_mode.receive_fifo_depth = SERIAL_RECEIVE_FIFO_DEPTH;
        serial.set_attributes(&io_mode)?;
        Ok(Serial { serial })
    }

    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Status> {
        // read() returns Ok if it managed to fill the whole buffer, or the error will contain
        // the number of bytes read. The only error we're fine with is TIMEOUT, as we can simply
        // retry that (and we'll keep getting TIMEOUTs when nobody is talking to us). In case of
        // any other error, bail out.
        self.serial.read(buf).map(|_| buf.len()).or_else(|err| {
            if err.status() == Status::TIMEOUT {
                Ok(*err.data())
            } else {
                Err(err.status())
            }
        })
    }
}

impl<'boot> runtime::Channel for Serial<'boot> {
    type Error = Error<()>;

    fn send(&mut self, data: &[u8]) -> Result<(), Self::Error> {
        self.serial.write(data).discard_errdata()
    }

    // Try to fill the buffer, ignoring any timeout errors. Any other errors
    // are propagated upward.
    fn recv(&mut self, data: &mut [u8]) -> Result<(), Self::Error> {
        let mut bytes_read = 0;
        while bytes_read < data.len() {
            let len = self.read(&mut data[bytes_read..])?;
            if len > 0 {
                bytes_read += len;
            }
        }
        Ok(())
    }
}
