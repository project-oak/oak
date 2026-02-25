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

use http::uri::Uri;
use oak_file_utils::data_path;
use tempfile::TempDir;

async fn run_key_value_lookup_test(communication_channel: &str) {
    let wasm_path = data_path("oak_functions/examples/key_value_lookup/key_value_lookup.wasm");

    let tempdir = TempDir::new().expect("unable to create temporary directory for UDS");
    let tempfile = tempdir.path().join("socket");

    let uri: Uri = tempfile.to_str().unwrap().to_string().parse().unwrap();

    let mut _output = oak_functions_test_utils::run_oak_functions_containers_example_in_background(
        &wasm_path,
        "oak_functions_launcher/mock_lookup_data",
        communication_channel,
        uri.clone(),
    );

    // Wait for the server to start up.
    let mut client =
        oak_functions_test_utils::create_client(uri, std::time::Duration::from_secs(120)).await;

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

// The TAP interface (oak0) is a global resource, and only one of the test may
// use it at a time.
static TAP_PERMIT: tokio::sync::Semaphore = tokio::sync::Semaphore::const_new(1);

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_tap() {
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    let permit = TAP_PERMIT.acquire().await.unwrap();
    run_key_value_lookup_test("tap").await;
    drop(permit);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_tap_v6() {
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    let permit = TAP_PERMIT.acquire().await.unwrap();
    run_key_value_lookup_test("tap-v6").await;
    drop(permit);
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

    let port = portpicker::pick_unused_port().expect("failed to pick a port");

    let addr: Uri = format!("http://[::]:{port}").parse().unwrap();
    let _background = oak_functions_test_utils::run_oak_functions_containers_example_in_background(
        &wasm_path,
        "oak_functions_launcher/mock_lookup_data",
        "network",
        addr.clone(),
    );

    // Wait for the server to start up.
    let mut client =
        oak_functions_test_utils::create_client(addr.clone(), std::time::Duration::from_secs(120))
            .await;

    let response = client.invoke(b"xxxyyyzzz").await.expect("failed to invoke");
    assert_eq!(std::str::from_utf8(&response).unwrap(), "xxxyyyzzz");

    let addr = addr.to_string();

    // TODO(#4177): Check response in the integration test.
    // Run Java client via Bazel.
    oak_functions_test_utils::run_java_client(&addr).expect("java client failed");

    // TODO(#4177): Check response in the integration test.
    // Run C++ client via Bazel.
    let request = "--request={\"lat\":0,\"lng\":0}";
    oak_functions_test_utils::run_cc_client(&addr, request).expect("cc client failed");
}
