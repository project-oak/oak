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

use oak_restricted_kernel_sdk::{
    channel::{FileDescriptorChannel, Read, Write},
    entrypoint,
};

const MESSAGE_SIZE: usize = 1;

// Starts an echo server that reads single bytes from the channel and writes
// them back.
#[entrypoint]
fn start_echo_server() -> ! {
    log::info!("suo");
    let mut channel = FileDescriptorChannel::default();
    log::info!("channel");
    loop {
        let bytes = {
            let mut bytes: Vec<u8> = vec![0; MESSAGE_SIZE];
            log::info!("allocated bytes");
            channel.read_exact(&mut bytes).expect("couldn't read bytes");
            bytes
        };
        channel.write_all(&bytes).expect("couldn't write bytes");
    }
}
