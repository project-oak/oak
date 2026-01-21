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

use oak_file_utils::data_path;

async fn run_key_value_lookup_test(communication_channel: &str) {
    let wasm_path = data_path("oak_functions/examples/key_value_lookup/key_value_lookup.wasm");

    let (mut _output, port) =
        oak_functions_test_utils::run_oak_functions_containers_example_in_background(
            &wasm_path,
            "oak_functions_launcher/mock_lookup_data",
            communication_channel,
        );

    // Wait for the server to start up.
    let mut client =
        oak_functions_test_utils::create_client(port, std::time::Duration::from_secs(120)).await;

    let response = client.invoke(b"test_key").await.expect("failed to invoke");
    assert_eq!(response, b"test_value");
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_virtio() {
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    run_key_value_lookup_test("virtio-vsock").await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_network() {
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    run_key_value_lookup_test("network").await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_tap() {
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    run_key_value_lookup_test("tap").await;
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_echo() {
    env_logger::init();
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    let wasm_path = data_path("oak_functions/examples/echo/echo.wasm");

    let (_background, port) =
        oak_functions_test_utils::run_oak_functions_containers_example_in_background(
            &wasm_path,
            "oak_functions_launcher/mock_lookup_data",
            "network",
        );

    // Wait for the server to start up.
    let mut client =
        oak_functions_test_utils::create_client(port, std::time::Duration::from_secs(120)).await;

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
