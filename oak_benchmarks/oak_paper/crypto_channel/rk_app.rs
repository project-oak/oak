//
// Copyright 2026 The Project Oak Authors
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
use alloc::boxed::Box;

use log::error;
use message_stream::{MessageStream, NoiseMessageStream, OakServerChannelMessageStream};
use oak_channel::server::ServerChannelHandle;
use oak_restricted_kernel_sdk::{channel::FileDescriptorChannel, entrypoint};

fn new_server_channel() -> OakServerChannelMessageStream {
    OakServerChannelMessageStream::new(ServerChannelHandle::new(
        Box::<FileDescriptorChannel>::default(),
    ))
}

// Starts an echo server that uses the Oak communication channel:
// https://github.com/project-oak/oak/blob/main/oak_channel/SPEC.md
#[entrypoint]
fn start_test_server() -> ! {
    error!("Starting read/write loop");
    let mut message_stream = new_server_channel();
    let mode = message_stream.read_message();

    match mode.as_slice() {
        b"plaintext" => plaintext_mode(),
        b"noise" => noise_mode(),
        _ => panic!("unknown mode"),
    }
}

// In noise mode, we start by assuming an incoming handshake sequence.
// Once a channel is established,
// encrypted payload. Then the loop will restart.
fn noise_mode() -> ! {
    loop {
        let mut noise_message_stream = NoiseMessageStream::new_server(new_server_channel());
        let request = noise_message_stream.read_message();
        noise_message_stream.send_message(request.as_slice());
    }
}

fn plaintext_mode() -> ! {
    let mut message_stream = new_server_channel();
    loop {
        let request = message_stream.read_message();
        message_stream.send_message(request.as_slice());
    }
}
