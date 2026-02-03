//
// Copyright 2023 The Project Oak Authors
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

use oak_restricted_kernel_interface::{DERIVED_KEY_FD, syscall::read};
use oak_restricted_kernel_sdk::{
    channel::{FileDescriptorChannel, Read, Write},
    entrypoint,
};

// Continuously reads single bytes from the communication channel, XORs them
// with a byte from the derived key and sends them back.
#[entrypoint]
fn run_server() -> ! {
    let mut key = [0u8; 32];
    let mut byte = [0u8; 1];
    read(DERIVED_KEY_FD, &mut key[..]).expect("couldn't read derived key");
    let mut iter = key.iter().cycle();
    let mut channel = FileDescriptorChannel::default();
    loop {
        channel.read_exact(&mut byte[..]).expect("couldn't read bytes");
        byte[0] ^= iter.next().expect("iterator ran out");
        channel.write_all(&byte[..]).expect("couldn't write bytes");
    }
}
