//
// Copyright 2021 The Project Oak Authors
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

use crate::server::{create_and_start_server, WasmHandler};
use hyper::client::Client;

use std::fs;

extern crate test;
use test::Bencher;

const TEST_WASM_MODULE_PATH: &str = "testdata/non-oak-minimal.wasm";

#[tokio::test]
async fn test_server() {
    let _ = env_logger::builder().is_test(true).try_init();
    let port = 9999;
    let address = format!("[::]:{}", port);
    let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let wasm_module_bytes =
        fs::read(TEST_WASM_MODULE_PATH).expect("Couldn't read test Wasm module");

    let server_fut = create_and_start_server(&address, &wasm_module_bytes, notify_receiver);
    let client_fut = start_client(port, notify_sender);

    let (res, _) = tokio::join!(server_fut, client_fut);
    assert!(res.is_ok());
}

async fn start_client(port: u16, notify_sender: tokio::sync::oneshot::Sender<()>) {
    let client = Client::new();
    let request = hyper::Request::builder()
        .method(http::Method::GET)
        .uri(format!("http://localhost:{}", port))
        .body(hyper::Body::empty())
        .unwrap();
    let _resp = client
        .request(request)
        .await
        .expect("Error while awaiting response");

    // TODO(#1919): Check the response.

    notify_sender
        .send(())
        .expect("Couldn't send completion signal.");
}

// TODO(#1933): Currently there is no support for running benchmark tests in the runner.
// Run this with: `cargo bench --manifest-path=oak_functions/loader/Cargo.toml`
#[bench]
fn bench_wasm_handler(bencher: &mut Bencher) {
    let summary = bencher.bench(|bencher| {
        let wasm_module_bytes =
            fs::read(TEST_WASM_MODULE_PATH).expect("Couldn't read test Wasm module");
        let wasm_handler =
            WasmHandler::create(&wasm_module_bytes).expect("Couldn't create the server");
        let request = hyper::Request::builder()
            .method(http::Method::GET)
            // We don't really send the request. So the URI can be anything. It is only needed for
            // building a valid request.
            .uri("example.com")
            .body(hyper::Body::empty())
            .unwrap();
        bencher.iter(|| wasm_handler.handle_request(&request));
    });

    // When running `cargo test` this benchmark test gets executed too, but `summary` will be `None`
    // in that case. So, here we first check that `summary` is not empty.
    if let Some(summary) = summary {
        // We expect the `mean` time for loading the test Wasm module and running its main function
        // to be less than 50ms.
        // Note: `summary.mean` is in nano seconds, even though it is not explicitly documented in
        // https://doc.rust-lang.org/test/stats/struct.Summary.html.
        assert!(summary.mean < 50_000.0);
    }
}
