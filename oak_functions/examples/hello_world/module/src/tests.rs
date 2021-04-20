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
use maplit::hashmap;
use oak_functions_loader::{logger::Logger, lookup::LookupData, server::create_and_start_server};
use std::{
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
};

const OAK_FUNCTIONS_SERVER_PORT: u16 = 9001;
const STATIC_SERVER_PORT: u16 = 9002;

#[tokio::test]
async fn test_server() {
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, OAK_FUNCTIONS_SERVER_PORT));
    let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("Cargo.toml");

    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"))
            .expect("Couldn't read Wasm module");

    let mock_static_server = Arc::new(test_utils::MockStaticServer::default());

    let mock_static_server_clone = mock_static_server.clone();
    tokio::spawn(async move { mock_static_server_clone.serve(STATIC_SERVER_PORT).await });

    mock_static_server.set_response_body(test_utils::serialize_entries(hashmap! {
        b"Harry".to_vec() => b"Potter".to_vec(),
        b"Sirius".to_vec() => b"Black".to_vec(),
        b"Ron".to_vec() => b"Weasley".to_vec(),
    }));

    let logger = Logger::for_test();

    let lookup_data = Arc::new(LookupData::new_empty(
        &format!("http://localhost:{}", STATIC_SERVER_PORT),
        logger.clone(),
    ));
    lookup_data.refresh().await.unwrap();

    let server_join_handle = tokio::spawn(async move {
        create_and_start_server(
            &address,
            &wasm_module_bytes,
            lookup_data,
            notify_receiver,
            logger,
        )
        .await
    });

    {
        // No lookup match.
        let response_fut = make_request(OAK_FUNCTIONS_SERVER_PORT, b"World").await;
        assert_eq!(
            "Hello World!\n",
            std::str::from_utf8(response_fut.as_slice()).unwrap()
        );
    }
    {
        // Lookup match.
        let response_fut = make_request(OAK_FUNCTIONS_SERVER_PORT, b"Harry").await;
        assert_eq!(
            "Hello Harry Potter!\n",
            std::str::from_utf8(response_fut.as_slice()).unwrap()
        );
    }

    notify_sender
        .send(())
        .expect("Couldn't send completion signal.");

    let res = server_join_handle.await.unwrap();
    assert!(res.is_ok());
}

async fn make_request(port: u16, request_body: &[u8]) -> Vec<u8> {
    let client = Client::new();
    let request = hyper::Request::builder()
        .method(http::Method::POST)
        .uri(format!("http://localhost:{}/invoke", port))
        .body(hyper::Body::from(request_body.to_vec()))
        .unwrap();
    let resp = client
        .request(request)
        .await
        .expect("Error while awaiting response");

    assert_eq!(resp.status(), hyper::StatusCode::OK);
    hyper::body::to_bytes(resp.into_body())
        .await
        .unwrap()
        .to_vec()
}
