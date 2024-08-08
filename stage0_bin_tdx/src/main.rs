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

#![no_std]
#![no_main]

use core::{panic::PanicInfo, ptr::addr_of};

use oak_stage0::paging;
use oak_tdx_guest::{
    tdcall::get_td_info,
    vmcall::{io_read_u8, io_write_u8},
};

mod asm;

#[no_mangle]
static mut TEST_DATA: u32 = 0;

static HELLO_OAK: &str = "Hello from stage0_bin_tdx!";

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

fn write_u32(n: u32) {
    let b = n.to_le_bytes();
    for c in b.iter().rev() {
        write_byte_hex(*c);
    }
    write_u8_to_serial(b'\n');
}

fn write_u64(n: u64) {
    let b = n.to_le_bytes();
    for c in b.iter().rev() {
        write_byte_hex(*c);
    }
    write_u8_to_serial(b'\n');
}

fn write_str(s: &str) {
    for c in s.bytes() {
        write_u8_to_serial(c);
    }
    write_u8_to_serial(b'\n');
}

fn debug_u32_variable(s: &str, val: u32) {
    for c in s.bytes() {
        write_u8_to_serial(c);
    }
    write_u8_to_serial(b':');
    write_u8_to_serial(b' ');
    write_u32(val);
}

fn debug_u64_variable(s: &str, val: u64) {
    for c in s.bytes() {
        write_u8_to_serial(c);
    }
    write_u8_to_serial(b':');
    write_u8_to_serial(b' ');
    write_u64(val);
}

fn init_tdx_serial_port() {
    io_write_u8(0x3f8 + 0x1, 0x0).unwrap(); // Disable interrupts
    io_write_u8(0x3f8 + 0x2, 0x0).unwrap(); // Disable FIFO
    io_write_u8(0x3f8 + 0x3, 0x3).unwrap(); // LINE_CONTROL_8N1
    io_write_u8(0x3f8 + 0x4, 0x3).unwrap(); // DATA_TERMINAL_READY_AND_REQUEST_TO_SEND
}
/// Entry point for the Rust code in the stage0 BIOS.
#[no_mangle]
pub extern "C" fn rust64_start() -> ! {
    init_tdx_serial_port();
    write_str(HELLO_OAK);
    debug_u32_variable(stringify!(TEST_DATA), unsafe { TEST_DATA });

    let td_info = get_td_info();
    debug_u64_variable(stringify!(td_info.gpa_width), td_info.gpa_width as u64);
    debug_u64_variable(stringify!(td_info.attributes), td_info.attributes.bits() as u64);
    debug_u32_variable(stringify!(td_info.max_vcpus), td_info.max_vcpus);
    debug_u32_variable(stringify!(td_info.num_vcpus), td_info.num_vcpus);

    loop {
        unsafe {
            assert_eq!(TEST_DATA, 0xdeadbeaf);
            assert!((addr_of!(TEST_DATA) as u64) < 0x200000);
        }
    }

    #[allow(unreachable_code)]
    oak_stage0::rust64_start()
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_stage0::panic(info)
}
