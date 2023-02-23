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

use lazy_static::lazy_static;
use oak_functions_launcher::schema::{self, InvokeRequest};
use oak_launcher_utils::launcher;
use std::{path::PathBuf, time::Duration};

lazy_static! {
    static ref ENCLAVE_BINARY_PATH: PathBuf = {
        let oak_functions_linux_fd_bin_path =
            oak_functions_test_utils::build_rust_crate_linux("oak_functions_linux_fd_bin")
                .expect("Failed to build oak_functions_linux_fd_bin");
        PathBuf::from(oak_functions_linux_fd_bin_path)
    };
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_virtual() {
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    xtask::testing::run_step(xtask::launcher::build_stage0()).await;
    xtask::testing::run_step(xtask::launcher::build_binary(
        "build Oak Restricted Kernel binary",
        xtask::launcher::OAK_RESTRICTED_KERNEL_BIN_DIR
            .to_str()
            .unwrap(),
    ))
    .await;
    let variant = xtask::launcher::LauncherMode::Virtual("oak_functions_enclave_app".to_string());
    xtask::testing::run_step(xtask::launcher::build_binary(
        "build Oak Functions enclave app",
        &variant.enclave_crate_path(),
    ))
    .await;

    let _background = xtask::testing::run_background(
        xtask::launcher::run_oak_functions_launcher_example(&variant),
    )
    .await;

    // Wait for the server to start up.
    tokio::time::sleep(Duration::from_secs(5)).await;

    let response = oak_functions_client::Client::new("http://localhost:8080")
        .await
        .unwrap()
        .invoke(b"test_key")
        .await
        .expect("failed to invoke");
    assert_eq!(response, b"test_value");
}

#[tokio::test]
async fn test_launcher_looks_up_key() {
    let params = launcher::native::Params {
        enclave_binary: ENCLAVE_BINARY_PATH.to_path_buf(),
    };

    // Make sure the response fits in the response size.
    let constant_response_size: u32 = 1024;

    let (launched_instance, connector_handle, _) = oak_functions_launcher::create(
        launcher::GuestMode::Native(params),
        xtask::launcher::MOCK_LOOKUP_DATA_PATH.to_path_buf(),
        xtask::launcher::WASM_PATH.to_path_buf(),
        constant_response_size,
    )
    .await
    .expect("Failed to create launcher");

    let mut client = schema::OakFunctionsAsyncClient::new(connector_handle);
    let body = b"test_key".to_vec();
    let invoke_request = InvokeRequest { body };

    let response = client
        .invoke(&invoke_request)
        .await
        .expect("Failed to receive response.");

    assert!(response.is_ok());
    assert_eq!(b"test_value".to_vec(), response.unwrap().body);

    launched_instance
        .kill()
        .await
        .expect("Failed to stop launcher");
}

#[tokio::test]
#[ignore]
async fn test_load_large_lookup_data() {
    let params = launcher::native::Params {
        enclave_binary: ENCLAVE_BINARY_PATH.to_path_buf(),
    };

    // Initialize > 2 GiB of lookup data to hit the proto limits.
    let lookup_data_size = 2 * (2 << 30);
    let entry_size = 2 << 10;
    // The key in the lookup data maps to itself, so an entry has double key size.
    let mut entries = std::collections::HashMap::new(); // Vec::with_capacity(lookup_data_size / entry_size / 2);
    let entries_count = lookup_data_size / entry_size;

    let key_prefix = vec![0u8; (entry_size / 2) - 4];

    for i in 0..entries_count {
        let mut n = key_prefix.clone();
        n.append(&mut format!("{}", i).into_bytes());
        entries.insert(n.clone(), n);
    }

    let lookup_data_file = oak_functions_test_utils::write_to_temp_file(
        &oak_functions_test_utils::serialize_entries(entries),
    );

    let constant_response_size = (entry_size as u32 / 2) + 1024; // Add some margin be on the safe side.

    let status = oak_functions_launcher::create(
        launcher::GuestMode::Native(params),
        lookup_data_file.path().to_path_buf(),
        xtask::launcher::WASM_PATH.to_path_buf(),
        constant_response_size,
    )
    .await;

    // TODO(#3668): status is currently not ok and the test is expected to fail until we can load 2
    // GiB of lookup data.
    assert!(status.is_ok());

    let (launched_instance, connector_handle, _) = status.unwrap();

    let mut first_key = key_prefix.clone();
    first_key.append(&mut format!("{}", 1).into_bytes());

    let mut client = schema::OakFunctionsAsyncClient::new(connector_handle);
    let invoke_request = InvokeRequest {
        body: first_key.clone(),
    };

    let response = client
        .invoke(&invoke_request)
        .await
        .expect("Failed to receive response.");

    assert!(response.is_ok());
    assert_eq!(first_key, response.unwrap().body);

    let mut last_key = key_prefix.clone();
    last_key.append(&mut format!("{}", entries_count - 1).into_bytes());

    let invoke_request = InvokeRequest {
        body: last_key.clone(),
    };

    let response = client
        .invoke(&invoke_request)
        .await
        .expect("Failed to receive response.");

    assert!(response.is_ok());
    assert_eq!(last_key, response.unwrap().body);

    launched_instance
        .kill()
        .await
        .expect("Failed to stop launcher");
}
