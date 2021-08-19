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
use oak_functions_abi::proto::{Request, Response, StatusCode};
use oak_functions_loader::{
    grpc::create_and_start_grpc_server,
    logger::Logger,
    lookup::{parse_lookup_entries, LookupData, LookupDataAuth},
    server::{apply_policy, format_bytes, Policy, WasmHandler},
};
use prost::Message;
use std::{
    convert::TryInto,
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
    time::Duration,
};
use test::Bencher;
use test_utils::make_request;

const MANIFEST_PATH: &str = "examples/key_value_lookup/module/Cargo.toml";

#[tokio::test]
async fn test_valid_policy() {
    // Policy values are large enough to allow successful serving of the request, and responding
    // with the actual response from the Wasm module.
    let constant_processing_time = Duration::from_millis(200);
    let policy = Policy {
        constant_response_size_bytes: 100,
        constant_processing_time,
    };

    let scenario = |server_port: u16| async move {
        let result = make_request(server_port, br#"key_1"#).await;
        // Check that the processing time is within a reasonable range of
        // `constant_processing_time` specified in the policy.
        assert!(result.elapsed > constant_processing_time);
        assert!(
            (result.elapsed.as_millis() as f64)
                < 1.05 * constant_processing_time.as_millis() as f64,
            format!("elapsed time is: {:?}", result.elapsed)
        );

        let response = result.response;
        assert_eq!(StatusCode::Success as i32, response.status);
        assert_eq!(
            std::str::from_utf8(response.body().unwrap()).unwrap(),
            r#"value_1"#
        );
    };

    run_scenario_with_policy(scenario, policy).await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn test_long_response_time() {
    // The `constant_processing_time` is too low.
    let constant_processing_time = Duration::from_millis(10);
    let policy = Policy {
        constant_response_size_bytes: 100,
        constant_processing_time,
    };

    // So we expect the request to fail, with `response not available error`.
    let scenario = |server_port: u16| async move {
        let result = make_request(server_port, br#"key_1"#).await;
        // Check the elapsed time, allowing a margin of 10ms.
        let margin = Duration::from_millis(10);
        assert!(
            result.elapsed < constant_processing_time + margin,
            "elapsed: {:?}",
            result.elapsed
        );

        let response = result.response;
        assert_eq!(StatusCode::PolicyTimeViolation as i32, response.status);
        assert_eq!(
            std::str::from_utf8(response.body().unwrap()).unwrap(),
            "Reason: response not available."
        );
    };

    run_scenario_with_policy(scenario, policy).await;
}

/// Starts the server with the given policy, and runs the given test scenario.
///
/// A normal test scenario makes any number of requests and checks the responses. It has to be an
/// async function, with a single `u16` input argument as the `server_port`, and returning the unit
/// type (`()`).
async fn run_scenario_with_policy<F, S>(test_scenario: F, policy: Policy)
where
    F: FnOnce(u16) -> S,
    S: std::future::Future<Output = ()>,
{
    let server_port = test_utils::free_port();
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, server_port));

    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.pop();
    manifest_path.push(MANIFEST_PATH);
    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), false)
            .expect("Couldn't read Wasm module");

    let logger = Logger::for_test();

    let mock_static_server = Arc::new(test_utils::MockStaticServer::default());

    let mock_static_server_clone = mock_static_server.clone();
    let static_server_port = test_utils::free_port();
    let mock_static_server_background = test_utils::background(|term| async move {
        mock_static_server_clone
            .serve(static_server_port, term)
            .await
    });

    mock_static_server.set_response_body(test_utils::serialize_entries(hashmap! {
        b"key_0".to_vec() => br#"value_0"#.to_vec(),
        b"key_1".to_vec() => br#"value_1"#.to_vec(),
        b"key_2".to_vec() => br#"value_2"#.to_vec(),
    }));

    let lookup_data = Arc::new(LookupData::new_empty(
        &format!("http://localhost:{}", static_server_port),
        LookupDataAuth::default(),
        logger.clone(),
    ));
    lookup_data.refresh().await.unwrap();
    let tee_certificate = vec![];

    let server_background = test_utils::background(|term| async move {
        create_and_start_grpc_server(
            &address,
            tee_certificate,
            &wasm_module_bytes,
            lookup_data,
            None,
            policy,
            term,
            logger,
            None,
        )
        .await
    });

    // Wait for the server thread to make progress before starting the client. This is needed for a
    // more accurate measurement of the processing time, and to avoid `connection refused` from the
    // client in tests that run with multiple threads.
    tokio::time::sleep(Duration::from_secs(1)).await;

    test_scenario(server_port).await;

    let res = server_background.terminate_and_join().await;
    assert!(res.is_ok());

    mock_static_server_background.terminate_and_join().await;
}

#[bench]
fn bench_wasm_handler(bencher: &mut Bencher) {
    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.pop();
    manifest_path.push(MANIFEST_PATH);
    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"), true)
            .expect("Couldn't read Wasm module");

    let summary = bencher.bench(|bencher| {
        let logger = Logger::for_test();
        let static_server_port = test_utils::free_port();
        let lookup_data = Arc::new(LookupData::new_empty(
            &format!("http://localhost:{}", static_server_port),
            LookupDataAuth::default(),
            logger.clone(),
        ));
        let wasm_handler = WasmHandler::create(
            &wasm_module_bytes,
            lookup_data.clone(),
            Arc::new(None),
            logger,
            None,
        )
        .expect("Couldn't create the server");
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            let (terminate_static_server_tx, terminate_static_server_rx) =
                tokio::sync::oneshot::channel::<()>();
            let mock_static_server = Arc::new(test_utils::MockStaticServer::default());
            let mock_static_server_clone = mock_static_server.clone();
            let static_server_join_handle = tokio::spawn(async move {
                mock_static_server_clone
                    .serve(static_server_port, async {
                        terminate_static_server_rx.await.unwrap()
                    })
                    .await
            });

            mock_static_server.set_response_body(test_utils::serialize_entries(hashmap! {
                b"key_0".to_vec() => br#"value_0"#.to_vec(),
                b"key_1".to_vec() => br#"value_1"#.to_vec(),
                b"key_2".to_vec() => br#"value_2"#.to_vec(),
            }));

            lookup_data.refresh().await.unwrap();
            terminate_static_server_tx.send(()).unwrap();
            static_server_join_handle.await.unwrap();
        });
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
            elapsed < Duration::from_millis(3),
            "elapsed time: {:.0?}",
            elapsed
        );
    }
}

#[test]
fn parse_lookup_entries_empty() {
    let empty = vec![];
    let entries = parse_lookup_entries(empty.as_ref()).unwrap();
    assert!(entries.is_empty());
}

// Fix the serialized representation for testing by manually annotating individual bytes.
//
// See https://developers.google.com/protocol-buffers/docs/encoding#structure.
const ENTRY_0_LENGTH_DELIMITED: &[u8] = &[
    8,  // Message total length.
    10, // Field 1 key: (1<<3) | 2
    2,  // Field 1 length.
    14, 12, // Field 1 value.
    18, // Field 2 key: (2<<3) | 2
    2,  // Field 2 length.
    19, 88, // Field 2 value.
];

const ENTRY_1_LENGTH_DELIMITED: &[u8] = &[
    15, // Message total length.
    10, // Field 1 key: (1<<3) | 2
    5,  // Field 1 length.
    b'H', b'a', b'r', b'r', b'y', // Field 1 value.
    18,   // Field 2 key: (2<<3) | 2
    6,    // Field 2 length.
    b'P', b'o', b't', b't', b'e', b'r', // Field 2 value.
];

// Ensure that the serialized representation is correct.
#[test]
fn check_serialized_lookup_entries() {
    {
        let mut buf = vec![];
        let entry = oak_functions_abi::proto::Entry {
            key: vec![14, 12],
            value: vec![19, 88],
        };
        entry.encode_length_delimited(&mut buf).unwrap();
        assert_eq!(buf, ENTRY_0_LENGTH_DELIMITED);
    }
    {
        let mut buf = vec![];
        let entry = oak_functions_abi::proto::Entry {
            key: b"Harry".to_vec(),
            value: b"Potter".to_vec(),
        };
        entry.encode_length_delimited(&mut buf).unwrap();
        assert_eq!(buf, ENTRY_1_LENGTH_DELIMITED);
    }
}

#[test]
fn parse_lookup_entries_multiple_entries() {
    let mut buf = vec![];
    buf.append(&mut ENTRY_0_LENGTH_DELIMITED.to_vec());
    buf.append(&mut ENTRY_1_LENGTH_DELIMITED.to_vec());
    let entries = parse_lookup_entries(buf.as_ref()).unwrap();
    assert_eq!(entries.len(), 2);
    assert_eq!(entries.get(&[14, 12].to_vec()), Some(&vec![19, 88]));
    assert_eq!(entries.get(&b"Harry".to_vec()), Some(&b"Potter".to_vec()));
}

#[test]
fn parse_lookup_entries_multiple_entries_trailing() {
    let mut buf = vec![];
    buf.append(&mut ENTRY_0_LENGTH_DELIMITED.to_vec());
    buf.append(&mut ENTRY_1_LENGTH_DELIMITED.to_vec());
    // Add invalid trailing bytes.
    buf.append(&mut vec![1, 2, 3]);
    let res = parse_lookup_entries(buf.as_ref());
    assert!(res.is_err());
}

#[test]
fn parse_lookup_entries_invalid() {
    // Invalid bytes.
    let buf = vec![1, 2, 3];
    let res = parse_lookup_entries(buf.as_ref());
    assert!(res.is_err());
}

#[tokio::test]
async fn lookup_data_refresh() {
    let mock_static_server = Arc::new(test_utils::MockStaticServer::default());

    let static_server_port = test_utils::free_port();
    let mock_static_server_clone = mock_static_server.clone();
    let mock_static_server_background = test_utils::background(|term| async move {
        mock_static_server_clone
            .serve(static_server_port, term)
            .await
    });

    let lookup_data = crate::LookupData::new_empty(
        &format!("http://localhost:{}", static_server_port),
        LookupDataAuth::default(),
        Logger::for_test(),
    );
    assert!(lookup_data.is_empty());

    // Initially empty file, no entries.
    lookup_data.refresh().await.unwrap();
    assert!(lookup_data.is_empty());

    // Single entry.
    mock_static_server.set_response_body(ENTRY_0_LENGTH_DELIMITED.to_vec());
    lookup_data.refresh().await.unwrap();
    assert_eq!(lookup_data.len(), 1);
    assert_eq!(lookup_data.get(&[14, 12]), Some(vec![19, 88]));
    assert_eq!(lookup_data.get(b"Harry"), None);

    // Empty file again.
    mock_static_server.set_response_body(vec![]);
    lookup_data.refresh().await.unwrap();
    assert!(lookup_data.is_empty());

    // A different entry.
    mock_static_server.set_response_body(ENTRY_1_LENGTH_DELIMITED.to_vec());
    lookup_data.refresh().await.unwrap();
    assert_eq!(lookup_data.len(), 1);
    assert_eq!(lookup_data.get(&[14, 12]), None);
    assert_eq!(lookup_data.get(b"Harry"), Some(b"Potter".to_vec()));

    // Two entries.
    let mut buf = ENTRY_0_LENGTH_DELIMITED.to_vec();
    buf.append(&mut ENTRY_1_LENGTH_DELIMITED.to_vec());
    mock_static_server.set_response_body(buf);
    lookup_data.refresh().await.unwrap();
    assert_eq!(lookup_data.len(), 2);
    assert_eq!(lookup_data.get(&[14, 12]), Some(vec![19, 88]));
    assert_eq!(lookup_data.get(b"Harry"), Some(b"Potter".to_vec()));

    mock_static_server_background.terminate_and_join().await;
}

#[tokio::test]
async fn test_apply_policy() {
    // A valid constant response body size
    let size = 50;

    // A valid policy
    let policy = Policy {
        constant_response_size_bytes: size,
        constant_processing_time: Duration::from_millis(10),
    };

    {
        // Wasm response with small enough body is serialized with padding, and no other change
        let small_success_response = Response::create(StatusCode::Success, vec![b'x'; size]);
        let function = async move || Ok(small_success_response);
        let res = apply_policy(policy.try_into().unwrap(), function).await;
        assert!(res.is_ok());
        let response = res.unwrap();
        assert_eq!(response.status, StatusCode::Success as i32);
        assert_eq!(response.body.len(), policy.constant_response_size_bytes);
    }

    {
        // Success Wasm response with a large body is discarded, and replaced with an error response
        let large_success_response = Response::create(StatusCode::Success, vec![b'x'; size + 1]);
        let function = async move || Ok(large_success_response);
        let res = apply_policy(policy.try_into().unwrap(), function).await;
        assert!(res.is_ok());
        let response = res.unwrap();
        assert_eq!(response.status, StatusCode::PolicySizeViolation as i32);
        assert_eq!(response.body.len(), policy.constant_response_size_bytes);
    }
}

#[test]
fn test_format_bytes() {
    // Valid UTF-8 string.
    assert_eq!("🚀oak⭐", format_bytes("🚀oak⭐".as_bytes()));
    // Incorrect UTF-8 bytes, as per https://doc.rust-lang.org/std/string/struct.String.html#examples-3.
    assert_eq!("[0, 159, 146, 150]", format_bytes(&[0, 159, 146, 150]));
}
