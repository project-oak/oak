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

use alloc::boxed::Box;
use core::panic::PanicInfo;
use log::info;
use oak_channel::Channel;
use oak_echo_service::EchoService;
use oak_linux_boot_params::BootParams;

mod asm;

#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, rsi: &BootParams) -> ! {
    let channel = oak_restricted_kernel::start_kernel(rsi);
    info!("In main!");
    start_echo_server(channel)
}

// Starts an echo server that uses the Oak communication channel:
// https://github.com/project-oak/oak/blob/main/oak_channel/SPEC.md
fn start_echo_server(channel: Box<dyn Channel>) -> ! {
    let service = oak_echo_service::EchoServiceImpl::default();
    let server = service.serve();
    oak_channel::server::start_blocking_server_protobuf(channel, server)
        .expect("Runtime encountered an unrecoverable error");
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("Error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_restricted_kernel::panic(info);
}
