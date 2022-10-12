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
//

use crate::{
    logger::Logger,
    lookup_data::{parse_lookup_entries, LookupDataAuth, LookupDataRefresher, LookupDataSource},
    server::apply_policy,
};
use oak_functions_abi::{proto::ServerPolicy, Response, StatusCode};
use oak_functions_lookup::LookupDataManager;
use prost::Message;
use std::{
    io::{Seek, Write},
    sync::Arc,
};

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
async fn lookup_data_refresh_http() {
    let mock_static_server = Arc::new(test_utils::MockStaticServer::default());

    let static_server_port = test_utils::free_port();
    let mock_static_server_clone = mock_static_server.clone();
    let mock_static_server_background = test_utils::background(|term| async move {
        mock_static_server_clone
            .serve(static_server_port, term)
            .await
    });

    let lookup_data_manager = Arc::new(LookupDataManager::new_empty(Logger::for_test()));
    let lookup_data_refresher = LookupDataRefresher::new(
        Some(LookupDataSource::Http {
            url: format!("http://localhost:{}", static_server_port),
            auth: LookupDataAuth::default(),
        }),
        lookup_data_manager.clone(),
        Logger::for_test(),
    );
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert!(lookup_data.is_empty());

    // Initially empty file, no entries.
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert!(lookup_data.is_empty());

    // Single entry.
    mock_static_server.set_response_body(ENTRY_0_LENGTH_DELIMITED.to_vec());
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert_eq!(lookup_data.len(), 1);
    assert_eq!(lookup_data.get(&[14, 12]), Some(vec![19, 88]));
    assert_eq!(lookup_data.get(b"Harry"), None);

    // Empty file again.
    mock_static_server.set_response_body(vec![]);
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert!(lookup_data.is_empty());

    // A different entry.
    mock_static_server.set_response_body(ENTRY_1_LENGTH_DELIMITED.to_vec());
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert_eq!(lookup_data.len(), 1);
    assert_eq!(lookup_data.get(&[14, 12]), None);
    assert_eq!(lookup_data.get(b"Harry"), Some(b"Potter".to_vec()));

    // Two entries.
    let mut buf = ENTRY_0_LENGTH_DELIMITED.to_vec();
    buf.append(&mut ENTRY_1_LENGTH_DELIMITED.to_vec());
    mock_static_server.set_response_body(buf);
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert_eq!(lookup_data.len(), 2);
    assert_eq!(lookup_data.get(&[14, 12]), Some(vec![19, 88]));
    assert_eq!(lookup_data.get(b"Harry"), Some(b"Potter".to_vec()));

    mock_static_server_background.terminate_and_join().await;
}

#[tokio::test]
async fn lookup_data_refresh_file() {
    let temp_file = tempfile::NamedTempFile::new().unwrap();

    let lookup_data_manager = Arc::new(LookupDataManager::new_empty(Logger::for_test()));
    let lookup_data_refresher = LookupDataRefresher::new(
        Some(LookupDataSource::File(temp_file.path().to_path_buf())),
        lookup_data_manager.clone(),
        Logger::for_test(),
    );
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert!(lookup_data.is_empty());

    // Initially empty file, no entries.
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert!(lookup_data.is_empty());

    // Single entry.
    temp_file.as_file().set_len(0).unwrap();
    temp_file.as_file().rewind().unwrap();
    temp_file
        .as_file()
        .write_all(ENTRY_0_LENGTH_DELIMITED)
        .unwrap();
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert_eq!(lookup_data.len(), 1);
    assert_eq!(lookup_data.get(&[14, 12]), Some(vec![19, 88]));
    assert_eq!(lookup_data.get(b"Harry"), None);

    // Empty file again.
    temp_file.as_file().set_len(0).unwrap();
    temp_file.as_file().rewind().unwrap();
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert!(lookup_data.is_empty());

    // A different entry.
    temp_file.as_file().set_len(0).unwrap();
    temp_file.as_file().rewind().unwrap();
    temp_file
        .as_file()
        .write_all(ENTRY_1_LENGTH_DELIMITED)
        .unwrap();
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert_eq!(lookup_data.len(), 1);
    assert_eq!(lookup_data.get(&[14, 12]), None);
    assert_eq!(lookup_data.get(b"Harry"), Some(b"Potter".to_vec()));

    // Two entries.
    temp_file.as_file().set_len(0).unwrap();
    temp_file.as_file().rewind().unwrap();
    temp_file
        .as_file()
        .write_all(ENTRY_0_LENGTH_DELIMITED)
        .unwrap();
    temp_file
        .as_file()
        .write_all(ENTRY_1_LENGTH_DELIMITED)
        .unwrap();
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert_eq!(lookup_data.len(), 2);
    assert_eq!(lookup_data.get(&[14, 12]), Some(vec![19, 88]));
    assert_eq!(lookup_data.get(b"Harry"), Some(b"Potter".to_vec()));
}

#[tokio::test]
async fn lookup_data_refresh_no_lookup_source() {
    let lookup_data_manager = Arc::new(LookupDataManager::new_empty(Logger::for_test()));
    let lookup_data_refresher =
        LookupDataRefresher::new(None, lookup_data_manager.clone(), Logger::for_test());
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert!(lookup_data.is_empty());

    // Still empty, no errors.
    lookup_data_refresher.refresh().await.unwrap();
    let lookup_data = lookup_data_manager.create_lookup_data();
    assert!(lookup_data.is_empty());
}

#[tokio::test]
async fn test_apply_policy() {
    // A valid constant response body size
    let size: usize = 50;

    // A valid policy
    let policy = ServerPolicy {
        constant_response_size_bytes: size as u32,
        constant_processing_time_ms: 10,
    };

    {
        // Wasm response with small enough body is serialized with padding, and no other change
        let small_success_response = Response::create(StatusCode::Success, vec![b'x'; size]);
        let function = move || Ok(small_success_response);
        let res = apply_policy(policy.clone(), function).await;
        assert!(res.is_ok());
        let response = res.unwrap();
        assert_eq!(response.status, StatusCode::Success);
        assert_eq!(
            response.body.len(),
            policy.constant_response_size_bytes as usize
        );
    }

    {
        // Success Wasm response with a large body is discarded, and replaced with an error response
        let large_success_response = Response::create(StatusCode::Success, vec![b'x'; size + 1]);
        let function = || Ok(large_success_response);
        let res = apply_policy(policy.clone(), function).await;
        assert!(res.is_ok());
        let response = res.unwrap();
        assert_eq!(response.status, StatusCode::PolicySizeViolation);
        assert_eq!(
            response.body.len(),
            policy.constant_response_size_bytes as usize
        );
    }
}
