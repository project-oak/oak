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
use prost::Message;
use std::{
    fs,
    io::{Seek, Write},
};

extern crate test;
use std::net::{Ipv6Addr, SocketAddr};
use test::Bencher;

const TEST_WASM_MODULE_PATH: &str = "testdata/non-oak-minimal.wasm";
const OAK_FUNCTIONS_SERVER_PORT: u16 = 9001;

#[tokio::test]
async fn test_server() {
    let _ = env_logger::builder().is_test(true).try_init();
    let address = SocketAddr::from((Ipv6Addr::UNSPECIFIED, OAK_FUNCTIONS_SERVER_PORT));
    let (notify_sender, notify_receiver) = tokio::sync::oneshot::channel::<()>();

    let wasm_module_bytes =
        fs::read(TEST_WASM_MODULE_PATH).expect("Couldn't read test Wasm module");

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
        .body(hyper::Body::empty())
        .unwrap();
    let resp = client
        .request(request)
        .await
        .expect("Error while awaiting response");

    assert_eq!(resp.status(), hyper::StatusCode::OK);
    assert_eq!(hyper::body::to_bytes(resp.into_body()).await.unwrap(), "");

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
        let rt = tokio::runtime::Runtime::new().unwrap();
        bencher.iter(|| {
            let request = hyper::Request::builder()
                .method(http::Method::POST)
                // We don't really send the request. So the hostname can be anything. It is only
                // needed for building a valid request.
                .uri("http://example.com/invoke")
                .body(hyper::Body::empty())
                .unwrap();
            let resp = rt.block_on(wasm_handler.handle_request(request)).unwrap();
            assert_eq!(resp.status(), hyper::StatusCode::OK);
        });
    });

    // When running `cargo test` this benchmark test gets executed too, but `summary` will be `None`
    // in that case. So, here we first check that `summary` is not empty.
    if let Some(summary) = summary {
        // We expect the `mean` time for loading the test Wasm module and running its main function
        // to be less than a fixed threshold.
        // Note: `summary.mean` is in nanoseconds, even though it is not explicitly documented in
        // https://doc.rust-lang.org/test/stats/struct.Summary.html.
        assert!(summary.mean < 50_000.0, "elapsed time: {}ns", summary.mean);
    }
}

#[test]
fn load_lookup_entries_empty() {
    let _ = env_logger::builder().is_test(true).try_init();
    let empty = vec![];
    let entries = crate::load_lookup_entries(empty.as_ref()).unwrap();
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
        let entry = crate::proto::Entry {
            key: vec![14, 12],
            value: vec![19, 88],
        };
        entry.encode_length_delimited(&mut buf).unwrap();
        assert_eq!(buf, ENTRY_0_LENGTH_DELIMITED);
    }
    {
        let mut buf = vec![];
        let entry = crate::proto::Entry {
            key: b"Harry".to_vec(),
            value: b"Potter".to_vec(),
        };
        entry.encode_length_delimited(&mut buf).unwrap();
        assert_eq!(buf, ENTRY_1_LENGTH_DELIMITED);
    }
}

#[test]
fn load_lookup_entries_multiple_entries() {
    let _ = env_logger::builder().is_test(true).try_init();
    let mut buf = vec![];
    buf.append(&mut ENTRY_0_LENGTH_DELIMITED.to_vec());
    buf.append(&mut ENTRY_1_LENGTH_DELIMITED.to_vec());
    let entries = crate::load_lookup_entries(buf.as_ref()).unwrap();
    assert_eq!(entries.len(), 2);
    assert_eq!(entries.get(&[14, 12].to_vec()), Some(&vec![19, 88]));
    assert_eq!(entries.get(&b"Harry".to_vec()), Some(&b"Potter".to_vec()));
}

#[test]
fn load_lookup_entries_multiple_entries_trailing() {
    let _ = env_logger::builder().is_test(true).try_init();
    let mut buf = vec![];
    buf.append(&mut ENTRY_0_LENGTH_DELIMITED.to_vec());
    buf.append(&mut ENTRY_1_LENGTH_DELIMITED.to_vec());
    // Add invalid trailing bytes.
    buf.append(&mut vec![1, 2, 3]);
    let res = crate::load_lookup_entries(buf.as_ref());
    assert!(res.is_err());
}

#[test]
fn load_lookup_entries_invalid() {
    let _ = env_logger::builder().is_test(true).try_init();
    // Invalid bytes.
    let buf = vec![1, 2, 3];
    let res = crate::load_lookup_entries(buf.as_ref());
    assert!(res.is_err());
}

/// Truncates the provided file and resets the cursor to the beginning of the file.
fn truncate(file: &mut std::fs::File) {
    file.set_len(0).unwrap();
    file.seek(std::io::SeekFrom::Start(0)).unwrap();
}

#[test]
fn lookup_data_refresh() {
    let mut file = tempfile::NamedTempFile::new().unwrap();
    let file_path = file.path().to_str().unwrap();
    let lookup_data = crate::LookupData::new_empty(file_path);
    assert_eq!(lookup_data.len(), 0);

    // Initially empty file, no entries.
    lookup_data.refresh().unwrap();
    assert_eq!(lookup_data.len(), 0);

    // Single entry.
    truncate(file.as_file_mut());
    file.write_all(ENTRY_0_LENGTH_DELIMITED).unwrap();
    lookup_data.refresh().unwrap();
    assert_eq!(lookup_data.len(), 1);
    assert_eq!(lookup_data.get(&[14, 12]), Some(vec![19, 88]));
    assert_eq!(lookup_data.get(b"Harry"), None);

    // Empty file again.
    truncate(file.as_file_mut());
    lookup_data.refresh().unwrap();
    assert_eq!(lookup_data.len(), 0);

    // A different entry.
    truncate(file.as_file_mut());
    file.write_all(ENTRY_1_LENGTH_DELIMITED).unwrap();
    lookup_data.refresh().unwrap();
    assert_eq!(lookup_data.len(), 1);
    assert_eq!(lookup_data.get(&[14, 12]), None);
    assert_eq!(lookup_data.get(b"Harry"), Some(b"Potter".to_vec()));

    // Two entries.
    truncate(file.as_file_mut());
    file.write_all(ENTRY_0_LENGTH_DELIMITED).unwrap();
    file.write_all(ENTRY_1_LENGTH_DELIMITED).unwrap();
    lookup_data.refresh().unwrap();
    assert_eq!(lookup_data.len(), 2);
    assert_eq!(lookup_data.get(&[14, 12]), Some(vec![19, 88]));
    assert_eq!(lookup_data.get(b"Harry"), Some(b"Potter".to_vec()));
}
