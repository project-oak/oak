//
// Copyright 2024 The Project Oak Authors
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

use oak_functions_service::wasm::{WasmConfig, WasmHandler};
use oak_restricted_kernel_sdk::{
    attestation::InstanceEvidenceProvider,
    channel::{start_blocking_server, FileDescriptorChannel},
    crypto::InstanceEncryptionKeyHandle,
    entrypoint,
    utils::samplestore::StaticSampleStore,
};

#[entrypoint]
fn main() -> ! {
    #[cfg(feature = "deny_sensitive_logging")]
    {
        // Only log warnings and errors to reduce the risk of accidentally leaking
        // execution information through debug logs.
        log::set_max_level(log::LevelFilter::Warn);
    }
    let mut invocation_stats = StaticSampleStore::<1000>::new().unwrap();

    let encryption_key_handle =
        InstanceEncryptionKeyHandle::create().expect("couldn't encryption key");
    let evidencer = InstanceEvidenceProvider::create().expect("couldn't get evidence");
    let service = oak_functions_enclave_service::OakFunctionsService::<_, _, WasmHandler>::new(
        evidencer,
        Arc::new(encryption_key_handle),
        None,
        WasmConfig::default(),
    );
    let server =
        oak_functions_enclave_service::proto::oak::functions::OakFunctionsServer::new(service);
    start_blocking_server(Box::<FileDescriptorChannel>::default(), server, &mut invocation_stats)
        .expect("server encountered an unrecoverable error");
}
