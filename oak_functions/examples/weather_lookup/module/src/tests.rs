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

extern crate test;

use crate::Location;
use lookup_data_generator::data::generate_and_serialize_sparse_weather_entries;
use maplit::hashmap;
use oak_functions_abi::proto::{Request, StatusCode};
use oak_functions_loader::{
    grpc::{create_and_start_grpc_server, create_wasm_handler},
    logger::Logger,
    lookup::{parse_lookup_entries, LookupData, LookupDataAuth},
    server::{Policy, WasmHandler},
};
use std::{
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
    time::Duration,
};
use test::Bencher;
use test_utils::make_request;

#[tokio::test]
async fn test_server() {
    let server_port = test_utils::free_port();
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, server_port));

    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("Cargo.toml");

    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), false)
            .expect("Couldn't read Wasm module");

    let mock_static_server = Arc::new(test_utils::MockStaticServer::default());

    let mock_static_server_clone = mock_static_server.clone();
    let static_server_port = test_utils::free_port();
    let mock_static_server_background = test_utils::background(|term| async move {
        mock_static_server_clone
            .serve(static_server_port, term)
            .await
    });

    let key_0 = Location {
        latitude_millidegrees: 52_000,
        longitude_millidegrees: 0,
    }
    .to_bytes();
    let key_1 = Location {
        latitude_millidegrees: 14_000,
        longitude_millidegrees: -12_000,
    }
    .to_bytes();

    mock_static_server.set_response_body(test_utils::serialize_entries(hashmap! {
        b"index".to_vec() => [key_0.clone(), key_1.clone()].concat(),
        key_0 => br#"{"temperature_degrees_celsius":10}"#.to_vec(),
        key_1 => br#"{"temperature_degrees_celsius":42}"#.to_vec(),
    }));

    let logger = Logger::for_test();

    let lookup_data = Arc::new(LookupData::new_empty(
        &format!("http://localhost:{}", static_server_port),
        LookupDataAuth::default(),
        logger.clone(),
    ));
    lookup_data.refresh().await.unwrap();

    let policy = Policy {
        constant_response_size_bytes: 100,
        constant_processing_time: Duration::from_millis(200),
    };
    let tee_certificate = vec![];
    let wasm_handler = create_wasm_handler(
        &wasm_module_bytes,
        lookup_data,
        None,
        vec![],
        logger.clone(),
    )
    .expect("could not create wasm_handler");

    let server_background = test_utils::background(|term| async move {
        create_and_start_grpc_server(
            &address,
            wasm_handler,
            tee_certificate,
            policy,
            term,
            logger,
        )
        .await
    });

    {
        // Exact key_0.
        let response = make_request(server_port, br#"{"lat":52.0,"lon":0}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(
            r#"{"temperature_degrees_celsius":10}"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // Close to key_0.
        let response = make_request(server_port, br#"{"lat":52.1,"lon":-0.1}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(
            r#"{"temperature_degrees_celsius":10}"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // Close to key_1.
        let response = make_request(server_port, br#"{"lat":14.1,"lon":-12.1}"#)
            .await
            .response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(
            r#"{"temperature_degrees_celsius":42}"#,
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }
    {
        // Malformed request.
        let response = make_request(server_port, b"invalid - JSON").await.response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(
            "could not deserialize request as JSON: Error(\"expected value\", line: 1, column: 1)",
            std::str::from_utf8(response.body().unwrap()).unwrap()
        );
    }

    let res = server_background.terminate_and_join().await;
    assert!(res.is_ok());

    mock_static_server_background.terminate_and_join().await;
}

// Test for the example contained in the README.
#[test]
fn test_location_from_slice() {
    let value = Location {
        latitude_millidegrees: 14_120,
        longitude_millidegrees: -19_880,
    };
    let bytes = vec![0x00, 0x00, 0x37, 0x28, 0xFF, 0xFF, 0xB2, 0x58];
    assert_eq!(bytes, value.to_bytes(),);
    assert_eq!(value, Location::from_bytes(&bytes));
}

#[bench]
fn bench_wasm_handler(bencher: &mut Bencher) {
    // This benchmark test takes quite a long time when running with a realistic amount of lookup
    // data. By default it uses a smaller number of entries. To run the bench with realistic data
    // size, use `cargo bench --features large-bench`.
    #[cfg(not(feature = "large-bench"))]
    let (entry_count, elapsed_limit_millis) = (10_000, 25);
    #[cfg(feature = "large-bench")]
    let (entry_count, elapsed_limit_millis) = (200_000, 500);

    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("Cargo.toml");
    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), true)
            .expect("Couldn't read Wasm module");
    let mut rng = rand::thread_rng();
    let buf = generate_and_serialize_sparse_weather_entries(&mut rng, entry_count).unwrap();
    let entries = parse_lookup_entries(buf).unwrap();

    let lookup_data = Arc::new(LookupData::for_test(entries));
    let logger = Logger::for_test();
    let wasm_handler = WasmHandler::create(&wasm_module_bytes, lookup_data, logger, None)
        .expect("Couldn't create the server");
    let rt = tokio::runtime::Runtime::new().unwrap();

    let summary = bencher.bench(|bencher| {
        bencher.iter(|| {
            let request = Request {
                body: br#"{"lat":52.1,"lon":-0.1}"#.to_vec(),
            };
            let resp = rt
                .block_on(wasm_handler.clone().handle_invoke(request))
                .unwrap();
            assert_eq!(resp.status, StatusCode::Success as i32);
        });
    });

    // When running `cargo test` this benchmark test gets executed too, but `summary` will be `None`
    // in that case. So, here we first check that `summary` is not empty.
    if let Some(summary) = summary {
        // `summary.mean` is in nanoseconds, even though it is not explicitly documented in
        // https://doc.rust-lang.org/test/stats/struct.Summary.html.
        let elapsed = Duration::from_nanos(summary.mean as u64);
        // We expect the `mean` time for loading the test Wasm module and running its main function
        // to be less than a fixed threshold.
        assert!(
            elapsed < Duration::from_millis(elapsed_limit_millis),
            "elapsed time: {:.0?}",
            elapsed
        );
    }
}
