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
#![no_main]
#![feature(alloc_error_handler)]

extern crate alloc;

use alloc::{vec, vec::Vec};
use core::panic::PanicInfo;

use log::info;
use oak_channel::{Read, Write};
use oak_restricted_kernel_sdk::{FileDescriptorChannel, StderrLogger};

const MESSAGE_SIZE: usize = 1;

static LOGGER: StderrLogger = StderrLogger {};

#[no_mangle]
fn _start() -> ! {
    log::set_logger(&LOGGER).unwrap();
    log::set_max_level(log::LevelFilter::Debug);
    oak_enclave_runtime_support::init();
    main();
}

fn main() -> ! {
    info!("In main!");
    start_echo_server()
}

// Starts an echo server that reads single bytes from the channel and writes
// them back.
fn start_echo_server() -> ! {
    let mut channel = FileDescriptorChannel::default();
    loop {
        let bytes = {
            let mut bytes: Vec<u8> = vec![0; MESSAGE_SIZE];
            channel.read_exact(&mut bytes).expect("couldn't read bytes");
            bytes
        };
        channel.write_all(&bytes).expect("couldn't write bytes");
    }
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("PANIC: {}", info);
    oak_restricted_kernel_interface::syscall::exit(-1);
}
