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

use alloc::{boxed::Box, sync::Arc};
use core::panic::PanicInfo;
use log::info;
use oak_channel::Channel;
use oak_linux_boot_params::BootParams;
use oak_remote_attestation_amd::PlaceholderAmdAttestationGenerator;

#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, rsi: &BootParams) -> ! {
    let channel = oak_restricted_kernel::start_kernel(rsi);
    main(channel)
}

fn main(channel: Box<dyn Channel>) -> ! {
    info!("In main!");
    let service = oak_functions_service::OakFunctionsService::new(Arc::new(
        PlaceholderAmdAttestationGenerator,
    ));
    let server = oak_functions_service::schema::OakFunctionsServer::new(service);
    oak_channel::server::start_blocking_server(channel, server)
        .expect("server encountered an unrecoverable error");
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_restricted_kernel::panic(info);
}
