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

//! Simple I/O driver for communication between the guest and the host via
//! shared memory.

#![no_std]
#![feature(allocator_api)]
extern crate alloc;

use alloc::{collections::VecDeque, vec::Vec};
use core::alloc::Allocator;

use oak_sev_guest::io::{IoPortFactory, PortFactoryWrapper, PortReader, PortWrapper, PortWriter};
use x86_64::{PhysAddr, VirtAddr};

/// I/O port descriptor for a buffer.
pub struct BufferDescriptor {
    /// I/O port to use for the most significant bytes of the buffer
    /// guest-physical address.
    buffer_msb_port: u16,
    /// I/O port to use for the least significant bytes of the buffer
    /// guest-physical address.
    buffer_lsb_port: u16,
    /// I/O port to use for length of output messages.
    length_port: u16,
}

/// Default I/O ports for the output buffer.
pub const DEFAULT_OUTPUT_BUFFER: BufferDescriptor =
    BufferDescriptor { buffer_msb_port: 0x6421, buffer_lsb_port: 0x6422, length_port: 0x6423 };

/// Default I/O ports for the input buffer.
pub const DEFAULT_INPUT_BUFFER: BufferDescriptor =
    BufferDescriptor { buffer_msb_port: 0x6424, buffer_lsb_port: 0x6425, length_port: 0x6426 };

/// The length of the buffer that will be used for output messages.
pub const OUTPUT_BUFFER_LENGTH: usize = 4096;
/// The length of the buffer that will be used for input messages.
pub const INPUT_BUFFER_LENGTH: usize = 4096;

// TODO(#3394): Move to a shared crate.
/// Memory address translation function.
pub trait Translator: Fn(VirtAddr) -> Option<PhysAddr> {}
impl<X: Fn(VirtAddr) -> Option<PhysAddr>> Translator for X {}

/// The simple I/O channel driver implementation.
pub struct SimpleIo<'a, A: Allocator> {
    output_buffer: Vec<u8, &'a A>,
    input_buffer: Vec<u8, &'a A>,
    output_length_port: PortWrapper<u32>,
    input_length_port: PortWrapper<u32>,
}

impl<'a, A: Allocator> SimpleIo<'a, A> {
    pub fn new<VP: Translator>(
        io_port_factory: PortFactoryWrapper,
        translate: VP,
        output: BufferDescriptor,
        input: BufferDescriptor,
        alloc: &'a A,
    ) -> Result<Self, &'static str> {
        let mut output_buffer: Vec<u8, &'a A> = Vec::with_capacity_in(OUTPUT_BUFFER_LENGTH, alloc);
        output_buffer.resize(OUTPUT_BUFFER_LENGTH, 0);
        let mut input_buffer: Vec<u8, &'a A> = Vec::with_capacity_in(INPUT_BUFFER_LENGTH, alloc);
        input_buffer.resize(INPUT_BUFFER_LENGTH, 0);
        let output_length_port = io_port_factory.new_writer(output.length_port);
        let input_length_port = io_port_factory.new_reader(input.length_port);

        write_address(
            &io_port_factory,
            translate(VirtAddr::from_ptr(output_buffer.as_ptr()))
                .ok_or("couldn't translate VirtAddr to PhysAddr")?,
            output.buffer_msb_port,
            output.buffer_lsb_port,
        )?;
        write_address(
            &io_port_factory,
            translate(VirtAddr::from_ptr(input_buffer.as_ptr()))
                .ok_or("couldn't translate VirtAddr to PhysAddr")?,
            input.buffer_msb_port,
            input.buffer_lsb_port,
        )?;

        Ok(Self { output_buffer, input_buffer, output_length_port, input_length_port })
    }

    pub fn new_with_defaults<VP: Translator>(
        io_port_factory: PortFactoryWrapper,
        translate: VP,
        alloc: &'a A,
    ) -> Result<Self, &'static str> {
        SimpleIo::new(
            io_port_factory,
            translate,
            DEFAULT_OUTPUT_BUFFER,
            DEFAULT_INPUT_BUFFER,
            alloc,
        )
    }

    /// Reads the next available bytes from the input buffer, if any are
    /// available.
    pub fn read_bytes(&mut self) -> Option<VecDeque<u8>> {
        // Safety: we read the value as a u32 and validate it before using it.
        let length = unsafe { self.input_length_port.try_read().ok()? } as usize;

        // Use a memory fence to ensure the read from the device happens before the read
        // from the buffer.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Acquire);

        if length == 0 {
            return None;
        }

        // A length larger than the buffer size indicates a corrupt or malicious VMM
        // device implementation. This is probably not recoverable, so panic.
        assert!(length <= INPUT_BUFFER_LENGTH, "invalid simple IO input message length.");
        let mut result = VecDeque::with_capacity(length);
        result.extend(&self.input_buffer[..length]);

        Some(result)
    }

    /// Writes the data to the output buffer and notifies the host.
    ///
    /// Returns the number of bytes written, if any.
    pub fn write_bytes(&mut self, data: &[u8]) -> Result<usize, &'static str> {
        if data.is_empty() {
            return Ok(0);
        }

        let length = core::cmp::min(OUTPUT_BUFFER_LENGTH, data.len());
        self.output_buffer[..length].copy_from_slice(&data[..length]);

        // Use a memory fence to ensure that the data is written to the buffer before we
        // notify the VMM.
        core::sync::atomic::fence(core::sync::atomic::Ordering::Release);

        // Safety: this usage is safe, as we as only write an uninterpreted u32 value to
        // the port.
        unsafe {
            self.output_length_port.try_write(length as u32)?;

            // Read back how much the host was able to consume from the buffer. If the count
            // is less than 0, there was an error.
            self.output_length_port.try_read()
        }
        .and_then(|ret| {
            if (ret as isize) < 0 {
                Err("simple IO device returned an error")
            } else {
                Ok(ret as usize)
            }
        })
    }
}

fn write_address(
    io_port_factory: &PortFactoryWrapper,
    buffer_pointer: PhysAddr,
    msb_port: u16,
    lsb_port: u16,
) -> Result<(), &'static str> {
    // Split the 64-bit address into its least- and most significant bytes.
    let address = buffer_pointer.as_u64();
    let address_msb = (address >> 32) as u32;
    let address_lsb = address as u32;
    // Safety: this usage is safe, as we as only write uninterpreted u32 values to
    // the ports.
    unsafe {
        io_port_factory.new_writer(msb_port).try_write(address_msb)?;
        io_port_factory.new_writer(lsb_port).try_write(address_lsb)
    }
}
