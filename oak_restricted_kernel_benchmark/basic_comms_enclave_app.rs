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
use alloc::{boxed::Box, vec};

use oak_restricted_kernel_sdk::{
    channel::{FileDescriptorChannel, Read, Write},
    entrypoint,
};

// Starts an echo server that uses the Oak communication channel:
// https://github.com/project-oak/oak/blob/main/oak_channel/SPEC.md
//
// Simple command protocol loop, not robust to errors, meant only for this
// simple benchmark.
//
// Client sends command (1 - write to RK, 2 - read from RK)
// Client sends LE-encoded u32 size
// For 1 - write to RK: enclave writes bytes, and that's it.
// For 2 - read from RK: enclave reads bytes and then sends a single `1` to ack
// (to ensure client knows bytes were received.)
#[entrypoint]
fn start_test_server() -> ! {
    let mut fd = Box::<FileDescriptorChannel>::default();

    // Command: 1 - write to RK
    // Commmand: 2 - read from RK
    let mut command_buf = [0u8; 1];

    // Size to read or write.
    let mut size_buf = [0u8; 4];

    loop {
        // Get the command and payload size
        fd.read_exact(&mut command_buf).expect("failed to read message size");
        fd.read_exact(&mut size_buf).expect("failed to read message size");

        let mut payload = vec![0u8; u32::from_le_bytes(size_buf) as usize];

        if command_buf[0] == 1 {
            // Read from host
            fd.read_exact(&mut payload).expect("failed to reaad message");
            // Ack
            fd.write_all(&[1]).expect("failed to write ack");
        } else if command_buf[0] == 2 {
            // Write to host
            fd.write_all(payload.as_slice()).expect("failed to write message");
            // No ack needed.
        }
    }
}
