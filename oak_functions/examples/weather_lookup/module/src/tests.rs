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

use maplit::hashmap;
use oak_functions_abi::proto::StatusCode;
use oak_functions_loader::{
    grpc::create_and_start_grpc_server, logger::Logger, lookup::LookupData, server::Policy,
};
use std::{
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
    time::Duration,
};
use test_utils::make_request;

#[tokio::test]
async fn test_server() {
    let server_port = test_utils::free_port();
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, server_port));

    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("Cargo.toml");

    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("invalid target dir"))
            .expect("couldn't read Wasm module");

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

    let policy = Policy {
        constant_response_size_bytes: 100,
        constant_processing_time: Duration::from_millis(200),
    };
    let tee_certificate = vec![];

    let server_background = test_utils::background(|term| async move {
        create_and_start_grpc_server(
            &address,
            tee_certificate,
            &wasm_module_bytes,
            lookup_data,
            policy,
            term,
            logger,
        )
        .await
    });

    {
        // Lookup match.
        let response = make_request(server_port, br#"{"lat":52,"lon":0}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(
            r#"{"temperature_degrees_celsius":10}"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // Valid location but no lookup match.
        let response = make_request(server_port, br#"{"lat":19,"lon":88}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(
            r#"weather not found for location"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // Malformed request.
        let response = make_request(server_port, b"invalid - JSON").await.response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(
            "could not deserialize request as JSON",
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }

    let res = server_background.terminate_and_join().await;
    assert!(res.is_ok());

    mock_static_server_background.terminate_and_join().await;
}
