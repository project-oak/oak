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

//! Integration benchmarks for the Oak Functions Launcher.

#![feature(test)]

extern crate test;

use std::path::PathBuf;

use oak_client::verifier::extract_encryption_public_key;
use oak_crypto::encryptor::ClientEncryptor;
use oak_file_utils::data_path;
use oak_functions_launcher::LookupDataConfig;
use oak_launcher_utils::launcher;
use oak_micro_rpc::oak::functions::OakFunctionsAsyncClient;
use oak_proto_rust::oak::functions::InvokeRequest;
use prost::Message;
use test::Bencher;
use ubyte::ByteUnit;

struct OakFunctionsTestConfig {
    wasm_path: PathBuf,
    lookup_data_path: PathBuf,
    request: Vec<u8>,
    expected_response: Vec<u8>,
}

/// Runs a benchmark for the Oak Functions Launcher, invoking the given Wasm
/// module with the given request, measuring the latency of the invocation.
///
/// Similar to the integration test, but wrapped in a non-async function, and
/// invoking the Wasm module in the benchmark loop.
fn run_bench(b: &mut Bencher, config: &OakFunctionsTestConfig) {
    let runtime = tokio::runtime::Builder::new_multi_thread().enable_all().build().unwrap();
    let oak_restricted_kernel_orchestrator_app_path =
        data_path("enclave_apps/oak_orchestrator/oak_orchestrator");
    let oak_functions_enclave_app_path =
        data_path("enclave_apps/oak_functions_enclave_app/oak_functions_enclave_app");

    let params = launcher::Params {
        kernel: data_path(
            "oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin",
        ),
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(oak_functions_enclave_app_path),
        bios_binary: data_path("stage0_bin/stage0_bin"),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path,
        memory_size: Some("256M".to_string()),
        pci_passthrough: None,
        initial_data_version: launcher::InitialDataVersion::V0,
        communication_channel: launcher::CommunicationChannel::VirtioConsole,
        vm_type: launcher::VmType::Default,
    };
    log::debug!("launcher params: {:?}", params);

    // Make sure the response fits in the response size.
    let constant_response_size: u32 = 1024;

    let lookup_data_config = LookupDataConfig {
        lookup_data_path: config.lookup_data_path.to_path_buf(),
        update_interval: None,
        max_chunk_size: ByteUnit::Gibibyte(2),
    };

    let (launched_instance, connector_handle, initialize_response) = runtime
        .block_on(oak_functions_launcher::create(
            params,
            lookup_data_config,
            config.wasm_path.to_path_buf(),
            constant_response_size,
        ))
        .expect("Failed to create launcher");
    log::info!("created launcher instance");

    let evidence =
        initialize_response.evidence.expect("initialize response doesn't have public key info");
    let serialized_server_public_key =
        extract_encryption_public_key(&evidence).expect("couldn't extract encryption public key");

    let mut client_encryptor = ClientEncryptor::create(&serialized_server_public_key)
        .expect("couldn't create client encryptor");

    let mut client = OakFunctionsAsyncClient::new(connector_handle);
    let encrypted_request =
        client_encryptor.encrypt(&config.request, &[]).expect("could not encrypt request");
    #[allow(clippy::needless_update)]
    let invoke_request =
        InvokeRequest { encrypted_request: Some(encrypted_request), ..Default::default() };

    // Invoke the function once outside of the benchmark loop to make sure it's
    // ready.
    {
        log::debug!("invoking handle_user_request");
        let response = runtime
            .block_on(client.handle_user_request(&invoke_request))
            .expect("Failed to receive response.");
        log::debug!("received response {:?}", response);
        assert!(response.is_ok());

        // Only check this outside of the benchmark loop.
        let encrypted_response = response.unwrap().encrypted_response.unwrap();
        let (decrypted_response, _authenticated_data) =
            client_encryptor.decrypt(&encrypted_response).expect("could not decrypt response");
        let response: Result<Vec<u8>, micro_rpc::Status> =
            micro_rpc::ResponseWrapper::decode(decrypted_response.as_ref())
                .expect("could not decode response")
                .into();
        assert_eq!(response.unwrap(), config.expected_response);
    }

    // We need to make sure to block on the future returned by
    // `handle_user_request`, otherwise the benchmark will finish before the
    // request is sent.
    b.iter(|| {
        let response = runtime
            .block_on(client.handle_user_request(&invoke_request))
            .expect("Failed to receive response.");
        assert!(response.is_ok());
    });

    log::info!("stopping launcher");

    runtime.block_on(launched_instance.kill()).expect("Failed to stop launcher");
}

#[bench]
fn bench_key_value_lookup(b: &mut Bencher) {
    // See https://github.com/rust-cli/env_logger/#in-tests.
    let _ = env_logger::builder().is_test(true).filter_level(log::LevelFilter::Trace).try_init();

    let wasm_path = "oak_functions/examples/key_value_lookup/key_value_lookup.wasm";
    run_bench(
        b,
        &OakFunctionsTestConfig {
            wasm_path: wasm_path.into(),
            lookup_data_path: data_path("oak_functions_launcher/mock_lookup_data"),
            request: b"test_key".to_vec(),
            expected_response: b"test_value".to_vec(),
        },
    );
}
