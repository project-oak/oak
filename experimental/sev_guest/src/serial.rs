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

use crate::ghcb::{Ghcb, GhcbProtocol};
use core::fmt::Write;

/// The offset from the base address to the interrupt register.
const INTERRUPT_ENABLE: u16 = 1;
/// The offset from the base address to the FIFO control register.
const FIFO_CONTROL: u16 = 2;
/// The offset from the base address to the line control register.
const LINE_CONTROL: u16 = 3;
/// The offset from the base address to the modem control register.
const MODEM_CONTROL: u16 = 4;
/// The offset from the base address to the line status register.
const LINE_STATUS: u16 = 5;

/// Value of the interrupt register to disable all interrupts.
///
/// See <https://wiki.osdev.org/Serial_Ports#Interrupt_enable_register>.
const DISABLE_ALL_INTERRUPTS: u8 = 0;

/// Value of the FIFO register to disable FIFO.
///
/// See <http://www.larvierinehart.com/serial/serialadc/serial.htm#17>.
const DISABLE_FIFO: u8 = 0;

/// Value of the line control register to set the number of data bits to 8, no parity bits, and the
/// number of stop bits to 1.
///
/// See <https://en.wikipedia.org/wiki/8-N-1>.
/// Also see <http://www.larvierinehart.com/serial/serialadc/serial.htm#18>.
const LINE_CONTROL_8N1: u8 = 3;

/// Value of the modem control register to mark the data terminal ready and request to send data.
///
/// See <http://www.larvierinehart.com/serial/serialadc/serial.htm#19>.
const DATA_TERMINAL_READY_AND_REQUEST_TO_SEND: u8 = 3;

/// Value of the line status register indicating that the send bufffer is empty.
///
/// See <https://wiki.osdev.org/Serial_Ports#Line_status_register>.
const OUTPUT_EMPTY: u8 = 1 << 5;

/// Basic implementation that allows for writing to a serial port using the SEV-ES and SEV-SNP GHCB
/// IOIO protocol.
///
/// See section 4.1.2 in <https://developer.amd.com/wp-content/resources/56421.pdf>.
pub struct SerialPort<'a> {
    /// The base address of the serial port.
    base_address: u16,
    ghcb_protocol: GhcbProtocol<'a, Ghcb>,
}

impl<'a> SerialPort<'a> {
    /// Creates a new instance of a serial port with the given base address.
    ///
    /// # Safety
    ///
    /// This function is unsafe as callers must make sure that the base address represents a
    /// valid serial port device.
    pub unsafe fn new(base_address: u16, ghcb_protocol: GhcbProtocol<'a, Ghcb>) -> Self {
        Self {
            base_address,
            ghcb_protocol,
        }
    }

    /// Initializes the serial port for writing.
    ///
    /// We don't require interrupts or FIFO, and don't configure a maximum speed.
    pub fn init(&mut self) -> Result<(), &'static str> {
        self.ghcb_protocol
            .io_write_u8(self.base_address + INTERRUPT_ENABLE, DISABLE_ALL_INTERRUPTS)?;
        self.ghcb_protocol
            .io_write_u8(self.base_address + FIFO_CONTROL, DISABLE_FIFO)?;
        self.ghcb_protocol
            .io_write_u8(self.base_address + LINE_CONTROL, LINE_CONTROL_8N1)?;
        self.ghcb_protocol.io_write_u8(
            self.base_address + MODEM_CONTROL,
            DATA_TERMINAL_READY_AND_REQUEST_TO_SEND,
        )?;
        Ok(())
    }

    /// Wait until the output buffer is empty.
    pub fn wait_for_empty_output(&mut self) -> Result<(), &'static str> {
        while self
            .ghcb_protocol
            .io_read_u8(self.base_address + LINE_STATUS)?
            & OUTPUT_EMPTY
            != OUTPUT_EMPTY
        {
            core::hint::spin_loop();
        }
        Ok(())
    }

    /// Sends a byte of data via the serial port.
    pub fn send(&mut self, data: u8) -> Result<(), &'static str> {
        self.wait_for_empty_output()?;
        self.ghcb_protocol.io_write_u8(self.base_address, data)
    }
}

impl<'a> Write for SerialPort<'a> {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for byte in s.bytes() {
            self.send(byte).map_err(|_| core::fmt::Error)?;
        }
        Ok(())
    }
}
