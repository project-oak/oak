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

#![no_std]

use core::fmt::Write;

use oak_sev_guest::io::{IoPortFactory, PortReader, PortWriter};

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

/// Value of the line control register to set the number of data bits to 8, no
/// parity bits, and the number of stop bits to 1.
///
/// See <https://en.wikipedia.org/wiki/8-N-1>.
/// Also see <http://www.larvierinehart.com/serial/serialadc/serial.htm#18>.
const LINE_CONTROL_8N1: u8 = 3;

/// Value of the modem control register to mark the data terminal ready and
/// request to send data.
///
/// See <http://www.larvierinehart.com/serial/serialadc/serial.htm#19>.
const DATA_TERMINAL_READY_AND_REQUEST_TO_SEND: u8 = 3;

/// Value of the line status register indicating that the receive buffer is
/// full.
///
/// See <https://wiki.osdev.org/Serial_Ports#Line_status_register>.
const INPUT_FULL: u8 = 1;

/// Value of the line status register indicating that the send buffer is empty.
///
/// See <https://wiki.osdev.org/Serial_Ports#Line_status_register>.
const OUTPUT_EMPTY: u8 = 1 << 5;

/// Basic implementation that allows for writing to and reading from a serial
/// port.
///
/// Uses the SEV-ES and SEV-SNP GHCB IOIO protocol, or using direct port-based
/// IO, depending on which IO port factory is used in the wrapper enum.
///
/// See section 4.1.2 in <https://www.amd.com/system/files/TechDocs/56421-guest-hypervisor-communication-block-standardization.pdf> for more
/// information on the GHCB IOIO protocol.
pub struct SerialPort<F, R, W>
where
    F: IoPortFactory<'static, u8, R, W>,
    R: PortReader<u8> + 'static,
    W: PortWriter<u8> + 'static,
{
    /// The base address of the serial port.
    base_address: u16,
    /// The factory for creating port readers and writers.
    io_port_factory: F,
    /// The port writer for writing a byte of data.
    data_writer: W,
    /// The port reading for reading a byte of data.
    data_reader: R,
    /// The port reader for checking the line status.
    line_status: R,
}

impl<F, R, W> SerialPort<F, R, W>
where
    F: IoPortFactory<'static, u8, R, W>,
    R: PortReader<u8> + 'static,
    W: PortWriter<u8> + 'static,
{
    /// Creates a new instance of a serial port with the given base address.
    ///
    /// # Safety
    ///
    /// This function is unsafe as callers must make sure that the base address
    /// represents a valid serial port device.
    pub unsafe fn new(base_address: u16, io_port_factory: F) -> Self {
        let data_writer = io_port_factory.new_writer(base_address);
        let data_reader = io_port_factory.new_reader(base_address);
        let line_status = io_port_factory.new_reader(base_address + LINE_STATUS);
        Self { base_address, io_port_factory, data_writer, data_reader, line_status }
    }

    /// Initializes the serial port for writing.
    ///
    /// We don't require interrupts or FIFO, and don't configure a maximum
    /// speed.
    pub fn init(&mut self) -> Result<(), &'static str> {
        // Safety: writing to these ports is safe based on the requirement that a valid
        // base address was provided when creating this instance.
        unsafe {
            self.io_port_factory
                .new_writer(self.base_address + INTERRUPT_ENABLE)
                .try_write(DISABLE_ALL_INTERRUPTS)?;
            self.io_port_factory
                .new_writer(self.base_address + FIFO_CONTROL)
                .try_write(DISABLE_FIFO)?;
            self.io_port_factory
                .new_writer(self.base_address + LINE_CONTROL)
                .try_write(LINE_CONTROL_8N1)?;
            self.io_port_factory
                .new_writer(self.base_address + MODEM_CONTROL)
                .try_write(DATA_TERMINAL_READY_AND_REQUEST_TO_SEND)?;
        }
        Ok(())
    }

    /// Wait until the output buffer is empty.
    pub fn wait_for_empty_output(&mut self) -> Result<(), &'static str> {
        // Safety: reading from this ports is safe based on the requirement that a valid
        // base address was provided when creating this instance.
        unsafe {
            while self.line_status.try_read()? & OUTPUT_EMPTY != OUTPUT_EMPTY {
                core::hint::spin_loop();
            }
        }
        Ok(())
    }

    /// Sends a byte of data via the serial port.
    pub fn send(&mut self, data: u8) -> Result<(), &'static str> {
        self.wait_for_empty_output()?;
        // Safety: writing to this port is safe based on the requirement that a valid
        // base address was provided when creating this instance.
        unsafe { self.data_writer.try_write(data) }
    }

    /// Wait until the input buffer is full.
    pub fn wait_for_full_input(&mut self) -> Result<(), &'static str> {
        // Safety: reading from this ports is safe based on the requirement that a valid
        // base address was provided when creating this instance.
        unsafe {
            while self.line_status.try_read()? & INPUT_FULL != INPUT_FULL {
                core::hint::spin_loop();
            }
        }
        Ok(())
    }

    /// Receives a byte of data from the serial port.
    pub fn receive(&mut self) -> Result<u8, &'static str> {
        self.wait_for_full_input()?;
        // Safety: reading from this port is safe based on the requirement that a valid
        // base address was provided when creating this instance.
        unsafe { self.data_reader.try_read() }
    }
}

impl<F, R, W> Write for SerialPort<F, R, W>
where
    F: IoPortFactory<'static, u8, R, W>,
    R: PortReader<u8> + 'static,
    W: PortWriter<u8> + 'static,
{
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for byte in s.bytes() {
            self.send(byte).map_err(|_| core::fmt::Error)?;
        }
        Ok(())
    }
}
