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
#![feature(core_c_str)]
#![feature(core_ffi_c)]

use alloc::boxed::Box;
use core::panic::PanicInfo;
use log::info;
use oak_baremetal_communication_channel::Channel;
use oak_remote_attestation::handshaker::{AttestationBehavior, EmptyAttestationVerifier};
use oak_remote_attestation_amd::PlaceholderAmdAttestationGenerator;

mod asm;
mod bootparam;

#[no_mangle]
pub extern "C" fn rust64_start(_rdi: u64, rsi: &bootparam::BootParams) -> ! {
    let channel = oak_baremetal_kernel::start_kernel(rsi);
    main(channel)
}

fn main(channel: Box<dyn Channel>) -> ! {
    info!("In main!");
    let attestation_behavior =
        AttestationBehavior::create(PlaceholderAmdAttestationGenerator, EmptyAttestationVerifier);
    let runtime = oak_baremetal_runtime::RuntimeImplementation::new(attestation_behavior);
    let service = oak_baremetal_runtime::schema::TrustedRuntime::serve(runtime);
    oak_baremetal_communication_channel::server::start_blocking_server(channel, service)
        .expect("Runtime encountered an unrecoverable error");
}

#[alloc_error_handler]
fn out_of_memory(layout: ::core::alloc::Layout) -> ! {
    panic!("Error allocating memory: {:#?}", layout);
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    oak_baremetal_kernel::panic(info);
}
