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

//! Simple I/O driver for communication between the guest and the host via shared memory.

#![no_std]
extern crate alloc;

use alloc::{collections::VecDeque, vec, vec::Vec};
use core::{marker::PhantomData, result::Result};
use sev_guest::io::{IoPortFactory, PortReader, PortWriter};
use x86_64::{
    instructions::port::{PortReadOnly, PortWriteOnly},
    structures::paging::Translate,
    VirtAddr,
};

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

/// A Simple IO device implementation that uses direct port-based IO.
pub type RawSimpleIo<'a> = SimpleIo<'a, PortReadOnly<u32>, PortWriteOnly<u32>>;

/// The simple I/O channel driver implementation.
pub struct SimpleIo<'a, R: PortReader<u32> + 'a, W: PortWriter<u32> + 'a> {
    output_buffer: Vec<u8>,
    input_buffer: Vec<u8>,
    output_length_port: W,
    input_length_port: R,
    _phantom: PhantomData<&'a W>,
}

impl<'a, R, W> SimpleIo<'a, R, W>
where
    R: PortReader<u32> + 'a,
    W: PortWriter<u32> + 'a,
{
    pub fn new<F: IoPortFactory<'a, u32, R, W>, T: Translate>(
        io_port_factory: F,
        translate: &T,
        output_buffer_msb_port: u16,
        output_buffer_lsb_port: u16,
        output_length_port: u16,
        input_buffer_msb_port: u16,
        input_buffer_lsb_port: u16,
        input_length_port: u16,
    ) -> Result<Self, &'static str> {
        let output_buffer = vec![0; OUTPUT_BUFFER_LEGNTH];
        let input_buffer = vec![0; INPUT_BUFFER_LEGNTH];
        let output_length_port = io_port_factory.new_writer(output_length_port);
        let input_length_port = io_port_factory.new_reader(input_length_port);

        write_address(
            &io_port_factory,
            translate,
            VirtAddr::from_ptr(output_buffer.as_ptr()),
            output_buffer_msb_port,
            output_buffer_lsb_port,
        )?;
        write_address(
            &io_port_factory,
            translate,
            VirtAddr::from_ptr(input_buffer.as_ptr()),
            input_buffer_msb_port,
            input_buffer_lsb_port,
        )?;

        Ok(Self {
            output_buffer,
            input_buffer,
            output_length_port,
            input_length_port,
            _phantom: PhantomData,
        })
    }

    pub fn new_with_defaults<F: IoPortFactory<'a, u32, R, W>, T: Translate>(
        io_port_factory: F,
        translate: &T,
    ) -> Result<Self, &'static str> {
        SimpleIo::new(
            io_port_factory,
            translate,
            DEFAULT_OUTPUT_BUFFER_MSB_PORT,
            DEFAULT_OUTPUT_BUFFER_LSB_PORT,
            DEFAULT_OUTPUT_LENGTH_PORT,
            DEFAULT_INPUT_BUFFER_MSB_PORT,
            DEFAULT_INPUT_BUFFER_LSB_PORT,
            DEFAULT_INPUT_LENGTH_PORT,
        )
    }

    /// Reads the next available bytes from the input buffer, if any are available.
    pub fn read_bytes(&mut self) -> Option<VecDeque<u8>> {
        // Safety: we read the value as a u32 and validate it before using it.
        let length = unsafe { self.input_length_port.try_read().ok()? } as usize;

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
        self.output_buffer[..length].copy_from_slice(&data[..length]);

        // Use a memory fence to ensure that the data is written to the buffer before we notify the
        // VMM.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Release);

        // Safety: this usage is safe, as we as only write an uninterpreted u32 value to the port.
        unsafe {
            self.output_length_port.try_write(length as u32).ok()?;
        }

        Some(length)
    }
}

fn write_address<
    'a,
    R: PortReader<u32> + 'a,
    W: PortWriter<u32> + 'a,
    F: IoPortFactory<'a, u32, R, W>,
    T: Translate,
>(
    io_port_factory: &F,
    translate: &T,
    buffer_pointer: VirtAddr,
    msb_port: u16,
    lsb_port: u16,
) -> Result<(), &'static str> {
    // Split the 64-bit address into its least- and most significant bytes.
    let address = translate
        .translate_addr(buffer_pointer)
        .ok_or("Failed to translate VirtAddr to PhysAddr")?
        .as_u64();
    let address_msb = (address >> 32) as u32;
    let address_lsb = address as u32;
    // Safety: this usage is safe, as we as only write uninterpreted u32 values to the ports.
    unsafe {
        io_port_factory
            .new_writer(msb_port)
            .try_write(address_msb)?;
        io_port_factory.new_writer(lsb_port).try_write(address_lsb)
    }
}
