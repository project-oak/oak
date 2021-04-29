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
use oak_functions_abi::proto::{FunctionsResponse, FunctionsStatusCode};
use oak_functions_loader::{logger::Logger, lookup::LookupData, server::create_and_start_server};
use prost::Message;
use std::{
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
};

#[tokio::test]
async fn test_server() {
    let server_port = test_utils::free_port();
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, server_port));

    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("Cargo.toml");

    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"))
            .expect("Couldn't read Wasm module");

    let mock_static_server = Arc::new(test_utils::MockStaticServer::default());

    let mock_static_server_clone = mock_static_server.clone();
    let static_server_port = test_utils::free_port();
    let mock_static_server_background = test_utils::background(|term| async move {
        mock_static_server_clone
            .serve(static_server_port, term)
            .await
    });

    mock_static_server.set_response_body(test_utils::serialize_entries(hashmap! {
        b"52,0".to_vec() => br#"{"temperature_degrees_celsius":10}"#.to_vec(),
        b"14,12".to_vec() => br#"{"temperature_degrees_celsius":42}"#.to_vec(),
    }));

    let logger = Logger::for_test();

    let lookup_data = Arc::new(LookupData::new_empty(
        &format!("http://localhost:{}", static_server_port),
        logger.clone(),
    ));
    lookup_data.refresh().await.unwrap();

    let server_background = test_utils::background(|term| async move {
        create_and_start_server(
            &address,
            &wasm_module_bytes,
            lookup_data,
            None,
            term,
            logger,
        )
        .await
    });

    {
        // Lookup match.
        let response_fut = make_request(server_port, br#"{"lat":52,"lon":0}"#).await;
        let response = FunctionsResponse::decode(response_fut.as_ref()).unwrap();
        assert_eq!(FunctionsStatusCode::Success as i32, response.status,);
        assert_eq!(
            r#"{"temperature_degrees_celsius":10}"#,
            std::str::from_utf8(response.body.as_slice()).unwrap()
        );
    }
    {
        // Valid location but no lookup match.
        let response_fut = make_request(server_port, br#"{"lat":19,"lon":88}"#).await;
        let response = FunctionsResponse::decode(response_fut.as_ref()).unwrap();
        assert_eq!(FunctionsStatusCode::Success as i32, response.status,);
        assert_eq!(
            r#"weather not found for location"#,
            std::str::from_utf8(response.body.as_slice()).unwrap()
        );
    }
    {
        // Malformed request.
        let response_fut = make_request(server_port, b"invalid - JSON").await;
        let response = FunctionsResponse::decode(response_fut.as_ref()).unwrap();
        assert_eq!(FunctionsStatusCode::Success as i32, response.status,);
        assert_eq!(
            "could not deserialize request as JSON",
            std::str::from_utf8(response.body.as_slice()).unwrap()
        );
    }

    let res = server_background.terminate_and_join().await;
    assert!(res.is_ok());

    mock_static_server_background.terminate_and_join().await;
}

async fn make_request(port: u16, request_body: &[u8]) -> Vec<u8> {
    let client = Client::builder().http2_only(true).build_http();
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
