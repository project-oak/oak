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

use oak_channel::basic_framed::load_raw;
use oak_restricted_kernel_sdk::{entrypoint, FileDescriptorChannel};

// Starts an echo server that reads single bytes from the channel and writes
// them back.
#[entrypoint]
fn start() -> ! {
    log::info!("Orchestrator will load enclave app binary",);
    let mut channel = FileDescriptorChannel::default();
    let app = load_raw::<FileDescriptorChannel, 4096>(&mut channel).expect("failed to load");
    log::info!(
        "Orchestrator loaded enclave app binary, size: {}",
        app.len()
    );
    loop {}
}
