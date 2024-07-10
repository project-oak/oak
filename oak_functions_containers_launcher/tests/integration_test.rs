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

use std::time::Duration;

use oak_client::verifier::InsecureAttestationVerifier;
use oak_functions_client::OakFunctionsClient;
use xtask::workspace_path;

async fn run_key_value_lookup_test(communication_channel: &str) {
    let wasm_path = oak_functions_test_utils::rust_crate_wasm_out_path("key_value_lookup");

    let (mut _output, port) =
        oak_functions_test_utils::run_oak_functions_containers_example_in_background(
            &wasm_path,
            oak_functions_test_utils::MOCK_LOOKUP_DATA_PATH.to_str().unwrap(),
            communication_channel,
        );

    // Wait for the server to start up.
    tokio::time::sleep(Duration::from_secs(60)).await;

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
async fn test_launcher_key_value_lookup_virtio() {
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    run_key_value_lookup_test("virtio-vsock").await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_network() {
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    run_key_value_lookup_test("network").await;
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_echo() {
    if xtask::testing::skip_test() {
        log::info!("skipping test");
        return;
    }

    let wasm_path = oak_functions_test_utils::rust_crate_wasm_out_path("echo");

    let (_background, port) =
        oak_functions_test_utils::run_oak_functions_containers_example_in_background(
            &wasm_path,
            oak_functions_test_utils::MOCK_LOOKUP_DATA_PATH.to_str().unwrap(),
            "network",
        );

    // Wait for the server to start up.
    tokio::time::sleep(Duration::from_secs(60)).await;

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
