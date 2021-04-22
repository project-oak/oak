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

use crate::{
    logger::Logger,
    lookup::{parse_lookup_entries, LookupData},
    server::{create_and_start_server, WasmHandler},
};
use hyper::{client::Client, Body};
use maplit::hashmap;
use prost::Message;
use std::{
    net::{Ipv6Addr, SocketAddr},
    sync::Arc,
    time::Duration,
};

extern crate test;
use test::Bencher;

const MANIFEST_PATH: &str = "examples/hello_world/module/Cargo.toml";

const OAK_FUNCTIONS_SERVER_PORT: u16 = 9001;
const STATIC_SERVER_PORT: u16 = 9002;

#[tokio::test]
async fn test_server() {
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, OAK_FUNCTIONS_SERVER_PORT));
    let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.pop();
    manifest_path.push(MANIFEST_PATH);
    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"))
            .expect("Couldn't read Wasm module");

    let logger = Logger::for_test();

    let mock_static_server = Arc::new(test_utils::MockStaticServer::default());

    let mock_static_server_clone = mock_static_server.clone();
    tokio::spawn(async move { mock_static_server_clone.serve(STATIC_SERVER_PORT).await });

    mock_static_server.set_response_body(test_utils::serialize_entries(hashmap! {
        b"52,0".to_vec() => br#"{"temperature_degrees_celsius":10}"#.to_vec(),
        b"14,12".to_vec() => br#"{"temperature_degrees_celsius":42}"#.to_vec(),
    }));

    let lookup_data = Arc::new(LookupData::new_empty(
        &format!("http://localhost:{}", STATIC_SERVER_PORT),
        logger.clone(),
    ));
    lookup_data.refresh().await.unwrap();

    let server_fut = create_and_start_server(
        &address,
        &wasm_module_bytes,
        lookup_data,
        notify_receiver,
        logger,
    );
    let client_fut = start_client(OAK_FUNCTIONS_SERVER_PORT, notify_sender);

    let (res, _) = tokio::join!(server_fut, client_fut);
    assert!(res.is_ok());
}

async fn start_client(port: u16, notify_sender: tokio::sync::oneshot::Sender<()>) {
    let client = Client::new();
    let request = hyper::Request::builder()
        .method(http::Method::POST)
        .uri(format!("http://localhost:{}/invoke", port))
        .body(Body::from(r#"{"lat":52,"lon":0}"#))
        .unwrap();
    let resp = client
        .request(request)
        .await
        .expect("Error while awaiting response");

    assert_eq!(resp.status(), hyper::StatusCode::OK);
    assert_eq!(
        hyper::body::to_bytes(resp.into_body()).await.unwrap(),
        r#"{"temperature_degrees_celsius":10}"#,
    );

    notify_sender
        .send(())
        .expect("Couldn't send completion signal.");
}

// TODO(#1933): Currently there is no support for running benchmark tests in the runner.
// Run this with: `cargo bench --manifest-path=oak_functions/loader/Cargo.toml`
#[bench]
fn bench_wasm_handler(bencher: &mut Bencher) {
    let mut manifest_path = std::env::current_dir().unwrap();
    manifest_path.pop();
    manifest_path.push(MANIFEST_PATH);
    let wasm_module_bytes =
        test_utils::compile_rust_wasm(manifest_path.to_str().expect("Invalid target dir"))
            .expect("Couldn't read Wasm module");

    let summary = bencher.bench(|bencher| {
        let logger = Logger::for_test();
        let lookup_data = Arc::new(LookupData::new_empty(
            &format!("http://localhost:{}", STATIC_SERVER_PORT),
            logger.clone(),
        ));
        let wasm_handler = WasmHandler::create(&wasm_module_bytes, lookup_data.clone(), logger)
            .expect("Couldn't create the server");
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            let mock_static_server = Arc::new(test_utils::MockStaticServer::default());

            let mock_static_server_clone = mock_static_server.clone();
            tokio::spawn(async move { mock_static_server_clone.serve(STATIC_SERVER_PORT).await });

            mock_static_server.set_response_body(test_utils::serialize_entries(hashmap! {
                b"52,0".to_vec() => br#"{"temperature_degrees_celsius":10}"#.to_vec(),
                b"14,12".to_vec() => br#"{"temperature_degrees_celsius":42}"#.to_vec(),
            }));

            lookup_data.refresh().await.unwrap();
        });
        bencher.iter(|| {
            let request = hyper::Request::builder()
                .method(http::Method::POST)
                // We don't really send the request. So the hostname can be anything. It is only
                // needed for building a valid request.
                .uri("http://example.com/invoke")
                .body(Body::from(r#"{"lat":52,"lon":0}"#))
                .unwrap();
            let resp = rt.block_on(wasm_handler.handle_request(request)).unwrap();
            assert_eq!(resp.status(), hyper::StatusCode::OK);
            let body = rt
                .block_on(hyper::body::to_bytes(resp.into_body()))
                .unwrap()
                .to_vec();
            assert_eq!(
                std::str::from_utf8(&body).unwrap(),
                r#"{"temperature_degrees_celsius":10}"#
            );
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

    let mock_static_server_clone = mock_static_server.clone();
    tokio::spawn(async move { mock_static_server_clone.serve(STATIC_SERVER_PORT).await });

    let lookup_data = crate::LookupData::new_empty(
        &format!("http://localhost:{}", STATIC_SERVER_PORT),
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
}
