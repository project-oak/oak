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

use hyper::client::Client;
use oak_functions_loader::server::create_and_start_server;
use std::net::{Ipv6Addr, SocketAddr};

const WASM_MODULE_NAME: &str = "hello_world.wasm";
const EXPECTED_RESPONSE: &str = "Hello World!\n";
const OAK_FUNCTIONS_SERVER_PORT: u16 = 9001;

#[tokio::test]
async fn test_server() {
    let _ = env_logger::builder().is_test(true).try_init();
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, OAK_FUNCTIONS_SERVER_PORT));
    let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("Cargo.toml");

    let wasm_module_bytes = test_utils::compile_rust_wasm(
        manifest_path.to_str().expect("Invalid target dir"),
        WASM_MODULE_NAME,
    )
    .expect("Couldn't read Wasm module");

    let server_fut = create_and_start_server(&address, &wasm_module_bytes, notify_receiver);
    let client_fut = start_client(OAK_FUNCTIONS_SERVER_PORT, notify_sender);

    let (res, _) = tokio::join!(server_fut, client_fut);
    assert!(res.is_ok());
}

async fn start_client(port: u16, notify_sender: tokio::sync::oneshot::Sender<()>) {
    let client = Client::new();
    let request = hyper::Request::builder()
        .method(http::Method::POST)
        .uri(format!("http://localhost:{}/invoke", port))
        .body(hyper::Body::from("World"))
        .unwrap();
    let resp = client
        .request(request)
        .await
        .expect("Error while awaiting response");

    assert_eq!(resp.status(), hyper::StatusCode::OK);
    assert_eq!(
        hyper::body::to_bytes(resp.into_body()).await.unwrap(),
        EXPECTED_RESPONSE
    );

    notify_sender
        .send(())
        .expect("Couldn't send completion signal.");
}
