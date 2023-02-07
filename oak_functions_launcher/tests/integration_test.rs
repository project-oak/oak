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

use oak_functions_launcher::{
    schema::{self, InvokeRequest},
    Mode,
};
use oak_functions_test_utils;
use std::path::PathBuf;

lazy_static! {
    static ref WASM_PATH: PathBuf = {
        // WORKSPACE_ROOT is set in .cargo/config.toml.
         [env!("WORKSPACE_ROOT"),"oak_functions_launcher", "key_value_lookup.wasm"].iter().collect()
    };

    static ref LOOKUP_DATA_PATH: PathBuf = {
        // WORKSPACE_ROOT is set in .cargo/config.toml.
         [env!("WORKSPACE_ROOT"),"oak_functions_launcher", "mock_lookup_data"].iter().collect()
    };

}

#[tokio::test]
async fn test_launcher_looks_up_key() {
    let oak_functions_linux_fd_bin_path =
        oak_functions_test_utils::build_rust_crate_linux("oak_functions_linux_fd_bin")
            .expect("Failed to build oak_functions_linux_fd_bin");

    let params = oak_functions_launcher::instance::native::Params {
        enclave_binary: PathBuf::from(oak_functions_linux_fd_bin_path),
    };

    let (launched_instance, connector_handle, _) = oak_functions_launcher::create(
        Mode::Native(params),
        LOOKUP_DATA_PATH.to_path_buf(),
        WASM_PATH.to_path_buf(),
        1024,
    )
    .await
    .expect("Fail to create launcher");

    let mut client = schema::OakFunctionsAsyncClient::new(connector_handle);
    let body = b"test_key".to_vec();
    let invoke_request = InvokeRequest { body: body };


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
