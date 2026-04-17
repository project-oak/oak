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

    let mut bg = oak_functions_test_utils::run_oak_functions_containers_example_in_background(
        &wasm_path,
        "oak_functions_launcher/mock_lookup_data",
        communication_channel,
        uri.clone(),
    );

    // Wait for the server to start up, but fail fast if the launcher exits.
    let mut client = tokio::select! {
        status = bg.wait() => panic!("launcher exited unexpectedly: {status:?}"),
        client = oak_functions_test_utils::create_client(uri, std::time::Duration::from_secs(120)) => client,
    };

    let response = client.invoke(b"test_key").await.expect("failed to invoke");
    assert_eq!(response, b"test_value");
}

fn should_run_test(test_index: usize) -> bool {
    let total_shards = match std::env::var("TEST_TOTAL_SHARDS") {
        Ok(val) => match val.parse::<usize>() {
            Ok(n) => n,
            Err(_) => return true,
        },
        Err(_) => return true,
    };

    let shard_index = match std::env::var("TEST_SHARD_INDEX") {
        Ok(val) => match val.parse::<usize>() {
            Ok(n) => n,
            Err(_) => return true,
        },
        Err(_) => return true,
    };

    if let Ok(status_file) = std::env::var("TEST_SHARD_STATUS_FILE") {
        let _ = std::fs::File::create(status_file);
    }

    test_index % total_shards == shard_index
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_virtio() {
    if !should_run_test(0) {
        return;
    }
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    run_key_value_lookup_test("virtio-vsock").await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_network() {
    if !should_run_test(1) {
        return;
    }
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    run_key_value_lookup_test("network").await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_tap() {
    if !should_run_test(2) {
        return;
    }
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    run_key_value_lookup_test("tap").await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_key_value_lookup_tap_v6() {
    if !should_run_test(3) {
        return;
    }
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    run_key_value_lookup_test("tap-v6").await;
}

// Allow enough worker threads to collect output from background tasks.
#[tokio::test(flavor = "multi_thread", worker_threads = 3)]
async fn test_launcher_echo() {
    if !should_run_test(4) {
        return;
    }
    env_logger::init();
    if oak_functions_test_utils::skip_test() {
        log::info!("skipping test");
        return;
    }

    let wasm_path = data_path("oak_functions/examples/echo/echo.wasm");

    let port = portpicker::pick_unused_port().expect("failed to pick a port");

    let addr: Uri = format!("http://[::]:{port}").parse().unwrap();
    let mut bg = oak_functions_test_utils::run_oak_functions_containers_example_in_background(
        &wasm_path,
        "oak_functions_launcher/mock_lookup_data",
        "network",
        addr.clone(),
    );

    // Wait for the server to start up, but fail fast if the launcher exits.
    let mut client = tokio::select! {
        status = bg.wait() => panic!("launcher exited unexpectedly: {status:?}"),
        client = oak_functions_test_utils::create_client(addr.clone(), std::time::Duration::from_secs(120)) => client,
    };

    let response = client.invoke(b"xxxyyyzzz").await.expect("failed to invoke");
    assert_eq!(std::str::from_utf8(&response).unwrap(), "xxxyyyzzz");

    let addr = addr.to_string();

    // TODO(#4177): Check response in the integration test.
    // Run C++ client via Bazel.
    let request = "--request={\"lat\":0,\"lng\":0}";
    oak_functions_test_utils::run_cc_client(&addr, request).expect("cc client failed");
}
