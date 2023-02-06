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

use std::path::PathBuf;

use lazy_static::lazy_static;
use micro_rpc::AsyncTransport;
use oak_functions_launcher::Mode;
use oak_functions_test_utils;

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
            .expect("Failed to build oak_functions_linux_fd_bin.");

    let params = oak_functions_launcher::instance::native::Params {
        enclave_binary: PathBuf::from(oak_functions_linux_fd_bin_path),
    };

    let (launched_instance, mut connector_handle, _) = oak_functions_launcher::create(
        Mode::Native(params),
        LOOKUP_DATA_PATH.to_path_buf(),
        WASM_PATH.to_path_buf(),
        // TODO(mschett): make sure the response fits in the constant response size.
        1024,
    )
    .await
    .expect("Fail to create launcher");

    // TODO(mschett): Find easiest way to send "test_key".
    // Send lookup request.
    let _ = connector_handle.invoke(&[42u8]).await;

    // TODO(mschett): Check lookup response "test_value".

    let _ = launched_instance.kill().await;
}
