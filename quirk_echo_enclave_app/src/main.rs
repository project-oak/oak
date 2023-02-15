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

use alloc::boxed::Box;
use core::panic::PanicInfo;
use log::info;
use oak_restricted_kernel_api::{FileDescriptorChannel, StderrLogger};

static LOGGER: StderrLogger = StderrLogger {};

// _start is the default entry point for a free-standing binary with [no_std] and
// [no_main] attributes.
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

// Starts an echo server that uses the Oak communication channel:
// https://github.com/project-oak/oak/blob/main/oak_channel/SPEC.md
fn start_echo_server() -> ! {
    let service = quirk_echo_service::EchoService::default();
    let server = quirk_echo_service::proto::EchoServer::new(service);
    oak_channel::server::start_blocking_server(Box::<FileDescriptorChannel>::default(), server)
        .expect("server encountered an unrecoverable error");
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("PANIC: {}", info);
    oak_restricted_kernel_api::syscall::exit(-1);
}
