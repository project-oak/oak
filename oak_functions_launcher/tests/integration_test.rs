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

use oak_crypto::{encryptor::ClientEncryptor, proto::oak::crypto::v1::EncryptedResponse};
use oak_functions_client::OakFunctionsClient;
use oak_functions_launcher::{
    proto::oak::functions::{InvokeRequest, OakFunctionsAsyncClient},
    update_lookup_data, LookupDataConfig,
};
use oak_launcher_utils::launcher;
use prost::Message;
use std::{io::Write, time::Duration};
use ubyte::ByteUnit;
use xtask::{launcher::MOCK_LOOKUP_DATA_PATH, workspace_path};

const EMPTY_ASSOCIATED_DATA: &[u8] = b"";

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_virtual() {
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

    let mut client = OakFunctionsClient::new(&format!("http://localhost:{port}"))
        .await
        .expect("failed to create client");

    let response = client.invoke(b"test_key").await.expect("failed to invoke");
    assert_eq!(response, b"test_value");
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_echo_virtual() {
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

    let mut client = OakFunctionsClient::new(&format!("http://localhost:{port}"))
        .await
        .expect("failed to create client");

    let response = client.invoke(b"xxxyyyzzz").await.expect("failed to invoke");
    assert_eq!(std::str::from_utf8(&response).unwrap(), "xxxyyyzzz");
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_weather_lookup_virtual() {
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("weather_lookup")
        .expect("Failed to build Wasm module");

    let (_background, port) = xtask::launcher::run_oak_functions_example_in_background(
        &wasm_path,
        workspace_path(&[
            "oak_functions",
            "examples",
            "weather_lookup",
            "testdata",
            "lookup_data_weather_sparse_s2",
        ])
        .to_str()
        .unwrap(),
    )
    .await;

    // Wait for the server to start up.
    tokio::time::sleep(Duration::from_secs(20)).await;

    let mut client = OakFunctionsClient::new(&format!("http://localhost:{port}"))
        .await
        .expect("failed to create client");

    let response = client
        .invoke(br#"{"lat":0,"lng":0}"#)
        .await
        .expect("failed to invoke");
    assert_eq!(
        std::str::from_utf8(&response).unwrap(),
        r#"{"temperature_degrees_celsius":29}"#
    );

    // TODO(#4177): Check response in the integration test.
    // Run Java client via Bazel.
    let status = tokio::process::Command::new("bazel")
        .arg("run")
        .arg("//java/src/main/java/com/google/oak/client/weather_lookup_client")
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

#[tokio::test]
async fn test_launcher_looks_up_key() {
    let oak_functions_linux_fd_bin_path =
        oak_functions_test_utils::build_rust_crate_linux("oak_functions_linux_fd_bin")
            .expect("Failed to build oak_functions_linux_fd_bin");

    let params = launcher::native::Params {
        enclave_binary: oak_functions_linux_fd_bin_path.into(),
    };

    // Make sure the response fits in the response size.
    let constant_response_size: u32 = 1024;

    let lookup_data_config = LookupDataConfig {
        lookup_data_path: xtask::launcher::MOCK_LOOKUP_DATA_PATH.to_path_buf(),
        update_interval: None,
        max_chunk_size: ByteUnit::Gibibyte(2),
    };

    let wasm_path = oak_functions_test_utils::build_rust_crate_wasm("key_value_lookup")
        .expect("Failed to build Wasm module");

    let (launched_instance, connector_handle, initialize_response) =
        oak_functions_launcher::create(
            launcher::GuestMode::Native(params),
            lookup_data_config,
            wasm_path.into(),
            constant_response_size,
        )
        .await
        .expect("Failed to create launcher");
    let server_encryption_public_key = initialize_response
        .public_key_info
        .expect("no public key info returned")
        .public_key;

    let mut client = OakFunctionsAsyncClient::new(connector_handle);
    let request_body = b"test_key".to_vec();

    // Encrypt request.
    let mut client_encryptor =
        ClientEncryptor::create(&server_encryption_public_key).expect("couldn't create encryptor");
    let encrypted_request = client_encryptor
        .encrypt(&request_body, EMPTY_ASSOCIATED_DATA)
        .expect("couldn't encrypt request");

    // Serialize request.
    let mut serialized_request = vec![];
    encrypted_request
        .encode(&mut serialized_request)
        .expect("couldn't serialize request");

    // Send invoke request.
    let invoke_request = InvokeRequest {
        body: serialized_request,
    };
    let invoke_response = client
        .invoke(&invoke_request)
        .await
        .expect("couldn't receive response");
    assert!(invoke_response.is_ok());
    let serialized_response = invoke_response.unwrap().body;

    // Deserialize response.
    let encrypted_response = EncryptedResponse::decode(serialized_response.as_ref())
        .expect("couldn't deserialize response");

    // Decrypt response.
    let (response, _) = client_encryptor
        .decrypt(&encrypted_response)
        .expect("client couldn't decrypt response");

    assert_eq!(std::str::from_utf8(&response).unwrap(), "test_value");

    launched_instance
        .kill()
        .await
        .expect("Failed to stop launcher");
}

#[tokio::test]
async fn test_load_large_lookup_data() {
    let oak_functions_linux_fd_bin_path =
        oak_functions_test_utils::build_rust_crate_linux("oak_functions_linux_fd_bin")
            .expect("Failed to build oak_functions_linux_fd_bin");

    let params = launcher::native::Params {
        enclave_binary: oak_functions_linux_fd_bin_path.into(),
    };

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
    let status_one_chunk = oak_functions_launcher::create(
        launcher::GuestMode::Native(params),
        lookup_data_config,
        wasm_path.into(),
        1024,
    )
    .await;
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
    let write_result = lookup_data_file.write_all(&oak_functions_test_utils::serialize_entries(
        enteries_two_chunks,
    ));
    assert!(write_result.is_ok());
    let status_two_chunks = update_lookup_data(&mut client, &lookup_data_config).await;
    assert!(status_two_chunks.is_ok());

    let enteries_four_chunks = oak_functions_test_utils::create_test_lookup_data(max_chunk_size, 4);
    let write_result = lookup_data_file.write_all(&oak_functions_test_utils::serialize_entries(
        enteries_four_chunks,
    ));
    assert!(write_result.is_ok());

    // Write 4 chunks in lookup data.
    let status_four_chunks = update_lookup_data(&mut client, &lookup_data_config).await;
    assert!(status_four_chunks.is_ok());

    launched_instance
        .kill()
        .await
        .expect("Failed to stop launcher");
}

#[ignore = "too expensive"]
#[tokio::test]
async fn test_load_two_gib_lookup_data() {
    let oak_functions_linux_fd_bin_path =
        oak_functions_test_utils::build_rust_crate_linux("oak_functions_linux_fd_bin")
            .expect("Failed to build oak_functions_linux_fd_bin");

    let params = launcher::native::Params {
        enclave_binary: oak_functions_linux_fd_bin_path.into(),
    };

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
    let status = oak_functions_launcher::create(
        launcher::GuestMode::Native(params),
        lookup_data_config,
        wasm_path.into(),
        1024,
    )
    .await;
    assert!(status.is_ok());
}
