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

use oak_functions_launcher::{
    proto::oak::functions::{InvokeRequest, OakFunctionsAsyncClient},
    LookupDataConfig,
};
use oak_launcher_utils::launcher;
use std::path::PathBuf;
use test::Bencher;
use ubyte::ByteUnit;

struct OakFunctionsTestConfig {
    wasm_path: PathBuf,
    lookup_data_path: PathBuf,
    request: Vec<u8>,
    expected_response: Vec<u8>,
}

/// Runs a benchmark for the Oak Functions Launcher, invoking the given Wasm module with the given
/// request, measuring the latency of the invocation.
///
/// Similar to the integration test, but wrapped in a non-async function, and invoking the Wasm
/// module in the benchmark loop.
fn run_bench(b: &mut Bencher, config: &OakFunctionsTestConfig) {
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .unwrap();

    let oak_functions_linux_fd_bin_path =
        oak_functions_test_utils::build_rust_crate_linux("oak_functions_linux_fd_bin")
            .expect("Failed to build oak_functions_linux_fd_bin");

    let params = launcher::native::Params {
        enclave_binary: oak_functions_linux_fd_bin_path.into(),
    };

    // Make sure the response fits in the response size.
    let constant_response_size: u32 = 1024;

    let lookup_data_config = LookupDataConfig {
        lookup_data_path: config.lookup_data_path.to_path_buf(),
        update_interval: None,
        max_chunk_size: ByteUnit::Gibibyte(2),
    };

    let (launched_instance, connector_handle, _) = runtime
        .block_on(oak_functions_launcher::create(
            launcher::GuestMode::Native(params),
            lookup_data_config,
            config.wasm_path.to_path_buf(),
            constant_response_size,
        ))
        .expect("Failed to create launcher");

    let mut client = OakFunctionsAsyncClient::new(connector_handle);
    let invoke_request = InvokeRequest {
        body: config.request.clone(),
    };

    // We need to make sure to block on the future returned by `invoke`, otherwise the benchmark
    // will finish before the request is sent.
    b.iter(|| {
        let response = runtime
            .block_on(client.invoke(&invoke_request))
            .expect("Failed to receive response.");
        assert!(response.is_ok());
        assert_eq!(config.expected_response, response.unwrap().body);
    });

    runtime
        .block_on(launched_instance.kill())
        .expect("Failed to stop launcher");
}

#[bench]
fn bench_key_value_lookup(b: &mut Bencher) {
    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup")
        .expect("Failed to build Wasm module");
    run_bench(
        b,
        &OakFunctionsTestConfig {
            wasm_path: wasm_path.into(),
            lookup_data_path: xtask::launcher::MOCK_LOOKUP_DATA_PATH.to_path_buf(),
            request: b"test_key".to_vec(),
            expected_response: b"test_value".to_vec(),
        },
    );
}
