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
#![feature(never_type)]

extern crate alloc;
use alloc::boxed::Box;

use oak_restricted_kernel_sdk::{
    attestation::InstanceAttester,
    channel::{start_blocking_server, FileDescriptorChannel},
    entrypoint,
    utils::samplestore::StaticSampleStore,
};

#[entrypoint]
fn start_server() -> ! {
    let mut invocation_stats = StaticSampleStore::<1000>::new().unwrap();
    let attester = InstanceAttester::create().expect("couldn't create attester");
    let service = service::EchoService { attester };
    let server = echo_service::sealed::codelabs::enclave::EnclaveServiceServer::new(service);
    start_blocking_server(Box::<FileDescriptorChannel>::default(), server, &mut invocation_stats)
        .expect("server encountered an unrecoverable error");
}
