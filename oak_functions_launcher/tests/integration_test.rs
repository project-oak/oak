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
// See the License for the speific language governing permissions and
// limitations under the License.

//! Integration tests for the Oak Functions Launcher.

use std::{io::Write, time::Duration};

use oak_file_utils::data_path;
use oak_functions_launcher::{update_lookup_data, LookupDataConfig};
use oak_launcher_utils::launcher;
use oak_micro_rpc::oak::functions::OakFunctionsAsyncClient;
use ubyte::ByteUnit;

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup() {
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    let wasm_path = "oak_functions/examples/key_value_lookup/key_value_lookup.wasm";

    let (mut _child, port) = oak_functions_test_utils::run_oak_functions_example_in_background(
        wasm_path,
        "oak_functions_launcher/mock_lookup_data",
    );

    // Wait for the server to start up.
    let mut client = oak_functions_test_utils::create_client(port, Duration::from_secs(120)).await;

    let response = client.invoke(b"test_key").await.expect("failed to invoke");
    assert_eq!(response, b"test_value");
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_echo() {
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    let wasm_path = "oak_functions/examples/echo/echo.wasm";

    let (_child, port) = oak_functions_test_utils::run_oak_functions_example_in_background(
        wasm_path,
        "oak_functions_launcher/mock_lookup_data",
    );

    // Wait for the server to start up.
    let mut client = oak_functions_test_utils::create_client(port, Duration::from_secs(120)).await;

    let response = client.invoke(b"xxxyyyzzz").await.expect("failed to invoke");
    assert_eq!(std::str::from_utf8(&response).unwrap(), "xxxyyyzzz");

    let addr = format!("http://localhost:{port}");

    // TODO(#4177): Check response in the integration test.
    // Run Java client via Bazel.
    oak_functions_test_utils::run_java_client(&addr).expect("java client failed");

    // TODO(#4177): Check response in the integration test.
    // Run C++ client via Bazel.
    let request = "--request={\"lat\":0,\"lng\":0}";
    oak_functions_test_utils::run_cc_client(&addr, request).expect("cc client failed");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_load_large_lookup_data() {
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    let oak_restricted_kernel_orchestrator_app_path =
        data_path("enclave_apps/oak_orchestrator/oak_orchestrator");
    let oak_functions_enclave_app_path =
        data_path("enclave_apps/oak_functions_enclave_app/oak_functions_enclave_app");

    let params = launcher::Params {
        kernel: data_path("oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin"),
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(oak_functions_enclave_app_path),
        bios_binary: data_path("stage0_bin/stage0_bin"),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path,
        memory_size: Some("2G".to_string()),
        pci_passthrough: None,
        initial_data_version: launcher::InitialDataVersion::V0,
        communication_channel: launcher::CommunicationChannel::VirtioConsole,
    };
    log::debug!("launcher params: {:?}", params);

    let max_chunk_size = ByteUnit::Kilobyte(2);

    // Initialize with 1 chunk.
    let entries_one_chunk = oak_functions_test_utils::create_test_lookup_data(max_chunk_size, 1);
    let mut lookup_data_file = oak_functions_test_utils::write_to_temp_file(
        &oak_functions_test_utils::serialize_entries(entries_one_chunk),
    );
    let lookup_data_config = LookupDataConfig {
        lookup_data_path: lookup_data_file.path().to_path_buf(),
        update_interval: None,
        max_chunk_size,
    };
    let wasm_path = "oak_functions/examples/key_value_lookup/key_value_lookup.wasm";
    let (launched_instance, connector_handle, _) =
        oak_functions_launcher::create(params, lookup_data_config, wasm_path.into(), 1024)
            .await
            .unwrap();

    let mut client = OakFunctionsAsyncClient::new(connector_handle);

    let lookup_data_config = LookupDataConfig {
        lookup_data_path: lookup_data_file.path().to_path_buf(),
        update_interval: None,
        max_chunk_size,
    };

    // Write 2 chunks in lookup data.
    let enteries_two_chunks = oak_functions_test_utils::create_test_lookup_data(max_chunk_size, 2);
    let write_result = lookup_data_file
        .write_all(&oak_functions_test_utils::serialize_entries(enteries_two_chunks));
    assert!(write_result.is_ok());
    let status_two_chunks = update_lookup_data(&mut client, &lookup_data_config).await;
    assert!(status_two_chunks.is_ok());

    let enteries_four_chunks = oak_functions_test_utils::create_test_lookup_data(max_chunk_size, 4);
    let write_result = lookup_data_file
        .write_all(&oak_functions_test_utils::serialize_entries(enteries_four_chunks));
    assert!(write_result.is_ok());

    // Write 4 chunks in lookup data.
    let status_four_chunks = update_lookup_data(&mut client, &lookup_data_config).await;
    assert!(status_four_chunks.is_ok());

    launched_instance.kill().await.expect("Failed to stop launcher");
}

#[ignore = "too expensive"]
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_load_two_gib_lookup_data() {
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    let oak_restricted_kernel_orchestrator_app_path =
        data_path("enclave_apps/oak_orchestrator/oak_orchestrator");
    let oak_functions_enclave_app_path =
        data_path("enclave_apps/oak_functions_enclave_app/oak_functions_enclave_app");

    let params = launcher::Params {
        kernel: data_path("oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin"),
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(oak_functions_enclave_app_path),
        bios_binary: data_path("stage0_bin/stage0_bin"),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path,
        memory_size: Some("256M".to_string()),
        pci_passthrough: None,
        initial_data_version: launcher::InitialDataVersion::V0,
        communication_channel: launcher::CommunicationChannel::VirtioConsole,
    };
    log::debug!("launcher params: {:?}", params);

    let max_chunk_size = ByteUnit::Gibibyte(2);
    // Initialize with 2 chunks.
    let entries_two_chunks = oak_functions_test_utils::create_test_lookup_data(max_chunk_size, 2);
    let lookup_data_file = oak_functions_test_utils::write_to_temp_file(
        &oak_functions_test_utils::serialize_entries(entries_two_chunks),
    );
    // This takes >5 min but will get there eventually.
    let lookup_data_config = LookupDataConfig {
        lookup_data_path: lookup_data_file.path().to_path_buf(),
        update_interval: None,
        max_chunk_size,
    };
    let wasm_path = "oak_functions/examples/key_value_lookup/key_value_lookup.wasm";
    let status =
        oak_functions_launcher::create(params, lookup_data_config, wasm_path.into(), 1024).await;
    assert!(status.is_ok());
}
