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

use crate::server::WasmServer;
use hyper::client::Client;

const WASM_MODULE_PATH: &str = "examples/modules/non-oak-minimal.wasm";

#[tokio::test]
async fn test_server() {
    let _ = env_logger::builder().is_test(true).try_init();
    let port = 9999;
    let address = format!("[::]:{}", port);
    let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let server =
        WasmServer::create(&address, WASM_MODULE_PATH).expect("Couldn't create the server");

    let server_fut = server.start(notify_receiver);
    let client_fut = create_client(port, notify_sender);

    let (res, _) = tokio::join!(server_fut, client_fut);
    assert!(res.is_ok());
}

async fn create_client(port: u16, notify_sender: tokio::sync::oneshot::Sender<()>) {
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

    notify_sender
        .send(())
        .expect("Couldn't send completion signal.");
}
