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

//! Simple I/O driver for communications between the guest and the host via shared memory.

#![no_std]
extern crate alloc;

use alloc::{collections::VecDeque, vec, vec::Vec};
use x86_64::instructions::port::{PortReadOnly, PortWriteOnly};

/// The default I/O port to use for the most significant bytes of the output buffer guest-physical
/// address.
pub const DEFAULT_OUTPUT_BUFFER_MSB_PORT: u16 = 0x6421;
/// The default I/O port to use for the least significant bytes of the output buffer guest-physical
/// address.
pub const DEFAULT_OUTPUT_BUFFER_LSB_PORT: u16 = 0x6422;
/// The default I/O port to use for the length of output messages.
pub const DEFAULT_OUTPUT_LENGTH_PORT: u16 = 0x6423;

/// The default I/O port to use for the most significant bytes of the input buffer guest-physical
/// address.
pub const DEFAULT_INPUT_BUFFER_MSB_PORT: u16 = 0x6424;
/// The default I/O port to use for the least significant bytes of the input buffer guest-physical
/// address.
pub const DEFAULT_INPUT_BUFFER_LSB_PORT: u16 = 0x6425;
/// The default I/O port to use for the length of input messages.
pub const DEFAULT_INPUT_LENGTH_PORT: u16 = 0x6426;

/// The length of the buffer that will be used for output messages.
pub const OUTPUT_BUFFER_LEGNTH: usize = 4096;
/// The length of the buffer that will be used for input messages.
pub const INPUT_BUFFER_LEGNTH: usize = 4096;

/// The simple I/O channel driver implementation.
pub struct SimpleIo {
    output_buffer: Vec<u8>,
    input_buffer: Vec<u8>,
    output_length_port: PortWriteOnly<u32>,
    input_length_port: PortReadOnly<u32>,
}

impl SimpleIo {
    pub fn new(
        output_buffer_msb_port: u16,
        output_buffer_lsb_port: u16,
        output_length_port: u16,
        input_buffer_msb_port: u16,
        input_buffer_lsb_port: u16,
        input_length_port: u16,
    ) -> Self {
        let output_buffer = vec![0; OUTPUT_BUFFER_LEGNTH];
        let input_buffer = vec![0; INPUT_BUFFER_LEGNTH];
        let output_length_port = PortWriteOnly::new(output_length_port);
        let input_length_port = PortReadOnly::new(input_length_port);

        write_address(
            output_buffer.as_ptr(),
            output_buffer_msb_port,
            output_buffer_lsb_port,
        );
        write_address(
            input_buffer.as_ptr(),
            input_buffer_msb_port,
            input_buffer_lsb_port,
        );

        Self {
            output_buffer,
            input_buffer,
            output_length_port,
            input_length_port,
        }
    }

    /// Reads the next available bytes from the input buffer, if any are available.
    pub fn read_bytes(&mut self) -> Option<VecDeque<u8>> {
        // Safety: we read the value as a u32 and validate it before using it.
        let length = unsafe { self.input_length_port.read() } as usize;

        // Use a memory fence to ensure the read from the device happens before the read from the
        // buffer.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Acquire);

        if length == 0 {
            return None;
        }

        // A length larger than the buffer size indicates a corrupt or malicious VMM device
        // implementation. This is probably not recoverable, so panic.
        assert!(
            length <= INPUT_BUFFER_LEGNTH,
            "Invalid simple IO input message length."
        );
        let mut result = VecDeque::with_capacity(length);
        result.extend(&self.input_buffer[..length]);

        Some(result)
    }

    /// Writes the data to the output buffer and notifies the host.
    ///
    /// Returns the number of bytes written, if any.
    pub fn write_bytes(&mut self, data: &[u8]) -> Option<usize> {
        if data.is_empty() {
            return None;
        }

        let length = core::cmp::min(OUTPUT_BUFFER_LEGNTH, data.len());
        self.output_buffer.copy_from_slice(&data[..length]);

        // Use a memory fence to ensure that the data is written to the buffer before we notify the
        // VMM.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Release);

        // Safety: this usage is safe, as we as only write an uninterpreted u32 value to the port.
        unsafe {
            self.output_length_port.write(length as u32);
        }

        Some(length)
    }
}

impl Default for SimpleIo {
    fn default() -> Self {
        Self::new(
            DEFAULT_OUTPUT_BUFFER_MSB_PORT,
            DEFAULT_OUTPUT_BUFFER_LSB_PORT,
            DEFAULT_OUTPUT_LENGTH_PORT,
            DEFAULT_INPUT_BUFFER_MSB_PORT,
            DEFAULT_INPUT_BUFFER_LSB_PORT,
            DEFAULT_INPUT_LENGTH_PORT,
        )
    }
}

fn write_address(buffer_pointer: *const u8, msb_port: u16, lsb_port: u16) {
    // Split the 64-bit address into its least- and most significant bytes.
    let address = get_guest_physiscal_address(buffer_pointer) as u64;
    let address_msb = (address >> 32) as u32;
    let address_lsb = address as u32;
    // Safety: this usage is safe, as we as only write uninterpreted u32 values to the ports.
    unsafe {
        PortWriteOnly::new(msb_port).write(address_msb);
        PortWriteOnly::new(lsb_port).write(address_lsb);
    }
}

fn get_guest_physiscal_address(pointer: *const u8) -> usize {
    // Assume identity mapping for now.
    pointer as usize
}
