//
// Copyright 2024 The Project Oak Authors
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

use oak_stage0::hal::PortFactory;
use oak_tdx_guest::vmcall::{
    io_read_u8, io_read_u16, io_read_u32, io_write_u8, io_write_u16, io_write_u32,
};

/// Creates a new [`PortFactory`] using the stage0 HAL interface.
pub fn port_factory() -> PortFactory {
    PortFactory {
        read_u8: |port| io_read_u8(port as u32),
        read_u16: |port| io_read_u16(port as u32),
        read_u32: |port| io_read_u32(port as u32),
        write_u8: |port, val| io_write_u8(port as u32, val),
        write_u16: |port, val| io_write_u16(port as u32, val),
        write_u32: |port, val| io_write_u32(port as u32, val),
    }
}

fn write_u8_to_serial(c: u8) {
    // wait_for_empty_output
    loop {
        if (io_read_u8(0x3f8 + 0x5).unwrap() & (1 << 5)) != 0 {
            break;
        }
    }
    io_write_u8(0x3f8, c).unwrap();
}

fn write_single_hex(c: u8) {
    if c < 0xa {
        write_u8_to_serial(c + (b'0'));
    } else {
        write_u8_to_serial(c - 10 + (b'a'));
    }
}

fn write_byte_hex(c: u8) {
    let char1 = (c >> 4) & 0xF;
    let char2 = c & 0xF;
    write_single_hex(char1);
    write_single_hex(char2);
}

fn write_bytes_hex(bytes: &[u8]) {
    for c in bytes.iter().rev() {
        write_byte_hex(*c);
    }
}

pub fn init_tdx_serial_port() {
    io_write_u8(0x3f8 + 0x1, 0x0).unwrap(); // Disable interrupts
    io_write_u8(0x3f8 + 0x2, 0x0).unwrap(); // Disable FIFO
    io_write_u8(0x3f8 + 0x3, 0x3).unwrap(); // LINE_CONTROL_8N1
    io_write_u8(0x3f8 + 0x4, 0x3).unwrap(); // DATA_TERMINAL_READY_AND_REQUEST_TO_SEND
}

pub trait Debug {
    fn debug(&self);
}

impl Debug for u32 {
    fn debug(&self) {
        self.to_le_bytes().as_slice().debug();
    }
}

impl Debug for u64 {
    fn debug(&self) {
        self.to_le_bytes().as_slice().debug();
    }
}

impl Debug for &str {
    fn debug(&self) {
        for c in self.bytes() {
            write_u8_to_serial(c);
        }
    }
}

impl Debug for &[u8] {
    fn debug(&self) {
        "0x".debug();
        write_bytes_hex(self)
    }
}

/// Output the provided arguments to the command line.
/// In order to be written, a type should implement the `Debug` trait
///
/// If you cast to a `str`, the bytes will be written as characters.
/// If you cast to a `&[u8]`, the hex representation of the bytes will be
/// written.
#[macro_export]
macro_rules! debug {
    ($($arg:expr),*) => {
        $($arg.debug();)*
        "\n".debug();
    };
}

pub use debug;
