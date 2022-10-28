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

use alloc::{boxed::Box, vec, vec::Vec};
use core::panic::PanicInfo;
use log::info;
use oak_channel::Channel;
use oak_linux_boot_params::BootParams;

mod asm;

const MESSAGE_SIZE: usize = 1;

#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, rsi: &BootParams) -> ! {
    let channel = oak_restricted_kernel::start_kernel(rsi);
    info!("In main!");
    start_echo_server(channel)
}

// Starts an echo server that reads single bytes from the channel and writes
// them back.
fn start_echo_server(mut channel: Box<dyn Channel>) -> ! {
    loop {
        let bytes = {
            let mut bytes: Vec<u8> = vec![0; MESSAGE_SIZE];
            channel.read(&mut bytes).expect("Couldn't read bytes");
            bytes
        };
        channel.write(&bytes).expect("Couldn't write bytes");
    }
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("Error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_restricted_kernel::panic(info);
}
