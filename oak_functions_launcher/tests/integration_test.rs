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

//! Integration tests for the Oak Functions Launcher.

use std::{io::Write, time::Duration};

use oak_client::verifier::InsecureAttestationVerifier;
use oak_functions_client::OakFunctionsClient;
use oak_functions_launcher::{
    proto::oak::functions::OakFunctionsAsyncClient, update_lookup_data, LookupDataConfig,
};
use oak_launcher_utils::launcher;
use ubyte::ByteUnit;
use xtask::{launcher::MOCK_LOOKUP_DATA_PATH, workspace_path};

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup() {
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup")
        .expect("Failed to build Wasm module");

    let (mut _background, port) = xtask::launcher::run_oak_functions_example_in_background(
        &wasm_path,
        MOCK_LOOKUP_DATA_PATH.to_str().unwrap(),
    )
    .await;

    // Wait for the server to start up.
    tokio::time::sleep(Duration::from_secs(20)).await;

    let mut client = OakFunctionsClient::new(
        &format!("http://localhost:{port}"),
        &InsecureAttestationVerifier {},
    )
    .await
    .expect("failed to create client");

    let response = client.invoke(b"test_key").await.expect("failed to invoke");
    assert_eq!(response, b"test_value");
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_echo() {
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("echo")
        .expect("Failed to build Wasm module");

    let (_background, port) = xtask::launcher::run_oak_functions_example_in_background(
        &wasm_path,
        MOCK_LOOKUP_DATA_PATH.to_str().unwrap(),
    )
    .await;

    // Wait for the server to start up.
    tokio::time::sleep(Duration::from_secs(20)).await;

    let mut client = OakFunctionsClient::new(
        &format!("http://localhost:{port}"),
        &InsecureAttestationVerifier {},
    )
    .await
    .expect("failed to create client");

    let response = client.invoke(b"xxxyyyzzz").await.expect("failed to invoke");
    assert_eq!(std::str::from_utf8(&response).unwrap(), "xxxyyyzzz");

    // TODO(#4177): Check response in the integration test.
    // Run Java client via Bazel.
    let status = tokio::process::Command::new("bazel")
        .arg("run")
        .arg("//java/src/main/java/com/google/oak/client/oak_functions_client")
        .arg("--")
        .arg(format!("http://localhost:{port}"))
        .current_dir(workspace_path(&[]))
        .spawn()
        .expect("failed to spawn bazel")
        .wait()
        .await
        .expect("failed to wait for bazel");
    eprintln!("bazel status: {:?}", status);
    assert!(status.success());

    // TODO(#4177): Check response in the integration test.
    // Run C++ client via Bazel.
    let status = tokio::process::Command::new("bazel")
        .arg("run")
        .arg("//cc/client:cli")
        .arg("--")
        .arg(format!("--address=localhost:{port}"))
        .arg("--request={\"lat\":0,\"lng\":0}")
        .current_dir(workspace_path(&[]))
        .spawn()
        .expect("failed to spawn bazel")
        .wait()
        .await
        .expect("failed to wait for bazel");
    eprintln!("bazel status: {:?}", status);
    assert!(status.success());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_load_large_lookup_data() {
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    xtask::testing::run_step(xtask::launcher::build_stage0()).await;
    xtask::testing::run_step(xtask::launcher::just_build("oak_restricted_kernel_wrapper")).await;

    let oak_restricted_kernel_orchestrator_app_path =
        oak_functions_test_utils::build_rust_crate_enclave("oak_orchestrator")
            .expect("Failed to build oak_orchestrator");

    let oak_functions_enclave_app_path =
        oak_functions_test_utils::build_rust_crate_enclave("oak_functions_enclave_app")
            .expect("Failed to build oak_functions_enclave_app");

    let params = launcher::Params {
        kernel: xtask::launcher::OAK_RESTRICTED_KERNEL_WRAPPER_BIN.clone(),
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(oak_functions_enclave_app_path.into()),
        bios_binary: workspace_path(&[
            "stage0_bin",
            "target",
            "x86_64-unknown-none",
            "release",
            "oak_stage0.bin",
        ]),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path.into(),
        memory_size: Some("256M".to_string()),
        pci_passthrough: None,
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
    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup")
        .expect("Failed to build Wasm module");
    let status_one_chunk =
        oak_functions_launcher::create(params, lookup_data_config, wasm_path.into(), 1024).await;
    assert!(status_one_chunk.is_ok());

    let (launched_instance, connector_handle, _) = status_one_chunk.unwrap();
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
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    xtask::testing::run_step(xtask::launcher::build_stage0()).await;
    xtask::testing::run_step(xtask::launcher::just_build("oak_restricted_kernel_wrapper")).await;

    let oak_restricted_kernel_orchestrator_app_path =
        oak_functions_test_utils::build_rust_crate_enclave("oak_orchestrator")
            .expect("Failed to build oak_orchestrator");

    let oak_functions_enclave_app_path =
        oak_functions_test_utils::build_rust_crate_enclave("oak_functions_enclave_app")
            .expect("Failed to build oak_functions_enclave_app");

    let params = launcher::Params {
        kernel: xtask::launcher::OAK_RESTRICTED_KERNEL_WRAPPER_BIN.clone(),
        vmm_binary: which::which("qemu-system-x86_64").unwrap(),
        app_binary: Some(oak_functions_enclave_app_path.into()),
        bios_binary: workspace_path(&[
            "stage0_bin",
            "target",
            "x86_64-unknown-none",
            "release",
            "oak_stage0.bin",
        ]),
        gdb: None,
        initrd: oak_restricted_kernel_orchestrator_app_path.into(),
        memory_size: Some("256M".to_string()),
        pci_passthrough: None,
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
    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup")
        .expect("Failed to build Wasm module");
    let status =
        oak_functions_launcher::create(params, lookup_data_config, wasm_path.into(), 1024).await;
    assert!(status.is_ok());
}
