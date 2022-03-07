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

use maplit::hashmap;
use oak_functions_abi::proto::{Request, ServerPolicy, StatusCode};
use oak_functions_loader::{
    grpc::{create_and_start_grpc_server, create_wasm_handler, RequestModel},
    logger::Logger,
    lookup::LookupFactory,
    lookup_data::{LookupData, LookupDataAuth, LookupDataSource},
    server::WasmHandler,
};
use std::{
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
    time::Duration,
};
use test::Bencher;
use test_utils::{get_config_info, make_request};

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

    mock_static_server.set_response_body(test_utils::serialize_entries(hashmap! {
        b"key_0".to_vec() => b"value_0".to_vec(),
        b"key_1".to_vec() => b"value_1".to_vec(),
        b"key_2".to_vec() => b"value_2".to_vec(),
        b"empty".to_vec() => vec![],
    }));

    let policy = ServerPolicy {
        constant_response_size_bytes: 100,
        constant_processing_time_ms: 200,
    };
    let tee_certificate = vec![];

    let logger = Logger::for_test();
    let lookup_data = Arc::new(LookupData::new_empty(
        Some(LookupDataSource::Http {
            url: format!("http://localhost:{}", static_server_port),
            auth: LookupDataAuth::default(),
        }),
        logger.clone(),
    ));
    lookup_data.refresh().await.unwrap();
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data, logger.clone())
        .expect("could not create LookupFactory");

    let wasm_handler =
        create_wasm_handler(&wasm_module_bytes, vec![lookup_factory], logger.clone())
            .expect("could not create wasm_handler");

    let server_background = test_utils::background(|term| async move {
        create_and_start_grpc_server(
            &address,
            wasm_handler,
            tee_certificate,
            policy.clone(),
            get_config_info(&wasm_module_bytes, policy, false, None),
            term,
            logger,
            RequestModel::BidiStreaming,
        )
        .await
    });

    {
        // Lookup match.
        let response = make_request(server_port, b"key_1").await.response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(b"value_1", response.body().unwrap(),);
    }
    {
        // Lookup fail.
        let response = make_request(server_port, b"key_42").await.response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(Vec::<u8>::new(), response.body().unwrap());
    }
    {
        // Lookup match but empty value.
        let response = make_request(server_port, b"empty").await.response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(Vec::<u8>::new(), response.body().unwrap());
    }

    let res = server_background.terminate_and_join().await;
    assert!(res.is_ok());

    mock_static_server_background.terminate_and_join().await;
}

#[bench]
fn bench_wasm_handler(bencher: &mut Bencher) {
    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.push("Cargo.toml");
    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), true)
            .expect("Couldn't read Wasm module");

    let logger = Logger::for_test();
    let entries = hashmap! {
        b"key_0".to_vec() => br#"value_0"#.to_vec(),
        b"key_1".to_vec() => br#"value_1"#.to_vec(),
        b"key_2".to_vec() => br#"value_2"#.to_vec(),
    };

    let lookup_data = Arc::new(LookupData::for_test(entries));
    let lookup_factory = LookupFactory::new_boxed_extension_factory(lookup_data, logger.clone())
        .expect("could not create LookupFactory");

    let wasm_handler = WasmHandler::create(&wasm_module_bytes, vec![lookup_factory], logger)
        .expect("Couldn't create the server");

    let rt = tokio::runtime::Runtime::new().unwrap();
    let summary = bencher.bench(|bencher| {
        bencher.iter(|| {
            let request = Request {
                body: br#"key_1"#.to_vec(),
            };
            let resp = rt
                .block_on(wasm_handler.clone().handle_invoke(request))
                .unwrap();
            assert_eq!(resp.status, StatusCode::Success as i32);
            assert_eq!(std::str::from_utf8(&resp.body).unwrap(), r#"value_1"#);
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
            elapsed < Duration::from_millis(5),
            "elapsed time: {:.0?}",
            elapsed
        );
    }
}
