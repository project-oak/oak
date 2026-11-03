//
// Copyright 2025 The Project Oak Authors
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

use std::sync::{Arc, atomic::Ordering};

use external_db_client::{
    DataBlobHandler, ExternalDbClient, MetadataBlobRead, MetadataPersistResult,
};
use private_memory_test_database_server_lib::service::SealedMemoryDatabaseServiceTestImpl;
use sealed_memory_rust_proto::oak::private_memory::{
    EncryptedDataBlob, EncryptedMetadataBlob, MetadataBlob, MetadataBlobNotModified,
    ReadMetadataBlobStreamResponse, read_metadata_blob_stream_response::Response,
};
use tokio::net::TcpListener;
use tonic::transport::Channel;

#[tokio::test]
async fn test_streaming_metadata_blob() {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();

    // Start the test database server
    tokio::spawn(async move {
        private_memory_test_database_server_lib::service::create(listener).await.unwrap();
    });

    let channel =
        Channel::from_shared(format!("http://{}", addr)).unwrap().connect().await.unwrap();
    let mut client = ExternalDbClient::new(channel);

    let id = "test_metadata_id".to_string();
    // 2MB data, should be split into 3 messages (1 MetadataBlob + 2 Chunks) since
    // CHUNK_SIZE is 1MB. The first message contains 1MB, and the next two
    // contain 512KB each? Wait, CHUNK_SIZE is 1024*1024.
    // If blob.len() is 2*1024*1024.
    // first_chunk_end = min(2MB, 1MB) = 1MB.
    // blob[1MB..] has 1MB left.
    // chunks(1MB) will give 1 chunk of 1MB.
    // Total 2 messages.
    let data = vec![0x42u8; 2 * 1024 * 1024];
    let metadata_blob = EncryptedMetadataBlob {
        encrypted_data_blob: Some(EncryptedDataBlob { nonce: vec![1, 2, 3], data: data.clone() }),
        version: "v1".to_string(),
    };

    // Test add_metadata_blob_stream
    let result = client
        .add_metadata_blob_stream(
            &id,
            &metadata_blob,
            prost_types::Timestamp { seconds: 1893456000, nanos: 0 },
        )
        .await
        .unwrap();
    // The test server appends "1" to the version on each write.
    assert_eq!(
        result,
        MetadataPersistResult::Succeeded { committed_version: Some("v11".to_string()) }
    );

    // Test get_metadata_blob_stream
    let retrieved = client
        .get_metadata_blob_stream(
            &id,
            prost_types::Timestamp { seconds: 1893456000, nanos: 0 },
            /* known_version= */ None,
        )
        .await
        .unwrap();
    let MetadataBlobRead::Blob(retrieved) = retrieved else {
        panic!("expected the blob, got {retrieved:?}");
    };
    assert_eq!(retrieved.version, "v11"); // Test server appends "1"
    let retrieved_data_blob = retrieved.encrypted_data_blob.unwrap();
    assert_eq!(retrieved_data_blob.data, data);
    assert_eq!(retrieved_data_blob.nonce, vec![1, 2, 3]);
}

#[tokio::test]
async fn test_streaming_metadata_blob_not_found() {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();

    tokio::spawn(async move {
        private_memory_test_database_server_lib::service::create(listener).await.unwrap();
    });

    let channel =
        Channel::from_shared(format!("http://{}", addr)).unwrap().connect().await.unwrap();
    let mut client = ExternalDbClient::new(channel);

    let retrieved = client
        .get_metadata_blob_stream(
            &"non_existent".to_string(),
            prost_types::Timestamp { seconds: 1893456000, nanos: 0 },
            /* known_version= */ None,
        )
        .await
        .unwrap();
    assert_eq!(retrieved, MetadataBlobRead::NotFound);
}

fn expiration() -> prost_types::Timestamp {
    prost_types::Timestamp { seconds: 1893456000, nanos: 0 }
}

/// Starts the test database server backed by `service` and returns a client.
async fn connect(service: Arc<SealedMemoryDatabaseServiceTestImpl>) -> ExternalDbClient {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();
    tokio::spawn(async move {
        private_memory_test_database_server_lib::service::serve(listener, service).await.unwrap();
    });
    let channel =
        Channel::from_shared(format!("http://{}", addr)).unwrap().connect().await.unwrap();
    ExternalDbClient::new(channel)
}

fn metadata_blob(version: &str) -> EncryptedMetadataBlob {
    EncryptedMetadataBlob {
        encrypted_data_blob: Some(EncryptedDataBlob { nonce: vec![1], data: vec![2] }),
        version: version.to_string(),
    }
}

#[tokio::test]
async fn test_metadata_blob_stream_with_known_version() {
    let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
    let mut client = connect(service.clone()).await;
    let id = "known_version_id".to_string();
    client.add_metadata_blob_stream(&id, &metadata_blob("v"), expiration()).await.unwrap();

    // The stored version is "v1": a matching known version isn't sent again.
    assert_eq!(
        client.get_metadata_blob_stream(&id, expiration(), Some("v1")).await.unwrap(),
        MetadataBlobRead::NotModified
    );
    // Any other known version gets the blob.
    let read = client.get_metadata_blob_stream(&id, expiration(), Some("v")).await.unwrap();
    assert!(matches!(&read, MetadataBlobRead::Blob(blob) if blob.version == "v1"), "{read:?}");
    // So does a host that ignores the known version.
    service.ignore_known_version.store(true, Ordering::SeqCst);
    let read = client.get_metadata_blob_stream(&id, expiration(), Some("v1")).await.unwrap();
    assert!(matches!(&read, MetadataBlobRead::Blob(blob) if blob.version == "v1"), "{read:?}");

    assert_eq!(service.metadata_not_modified_replies.load(Ordering::SeqCst), 1);
    assert_eq!(service.metadata_blob_downloads.load(Ordering::SeqCst), 2);
    assert_eq!(*service.metadata_stream_known_versions.lock().await, ["v1", "v", "v1"]);
}

fn not_modified() -> ReadMetadataBlobStreamResponse {
    ReadMetadataBlobStreamResponse {
        response: Some(Response::NotModified(MetadataBlobNotModified {})),
    }
}

fn blob_header(version: &str) -> ReadMetadataBlobStreamResponse {
    ReadMetadataBlobStreamResponse {
        response: Some(Response::MetadataBlob(MetadataBlob {
            data_blob: None,
            version: version.to_string(),
        })),
    }
}

fn chunk() -> ReadMetadataBlobStreamResponse {
    ReadMetadataBlobStreamResponse { response: Some(Response::Chunk(vec![1])) }
}

/// Streams that misuse `not_modified` are rejected.
#[tokio::test]
async fn test_metadata_blob_stream_rejects_invalid_not_modified() {
    let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
    let mut client = connect(service.clone()).await;
    let id = "invalid_not_modified_id".to_string();
    let cases: [(&str, Option<&str>, Vec<ReadMetadataBlobStreamResponse>); 4] = [
        ("not_modified without a known version", None, vec![not_modified()]),
        ("chunk after not_modified", Some("v1"), vec![not_modified(), chunk()]),
        ("not_modified after metadata_blob", Some("v1"), vec![blob_header("v2"), not_modified()]),
        ("not_modified twice", Some("v1"), vec![not_modified(), not_modified()]),
    ];
    for (name, known_version, messages) in cases {
        *service.next_metadata_stream_reply.lock().await = Some(messages);
        let read = client.get_metadata_blob_stream(&id, expiration(), known_version).await;
        assert!(read.is_err(), "{name}: {read:?}");
    }
}

#[tokio::test]
async fn test_metadata_write_without_committed_version() {
    let service = Arc::new(SealedMemoryDatabaseServiceTestImpl::default());
    service.omit_committed_version.store(true, Ordering::SeqCst);
    let mut client = connect(service).await;
    let id = "old_host_id".to_string();

    let result =
        client.add_metadata_blob_stream(&id, &metadata_blob("v"), expiration()).await.unwrap();
    assert_eq!(result, MetadataPersistResult::Succeeded { committed_version: None });

    // A stale version is still rejected.
    let result =
        client.add_metadata_blob_stream(&id, &metadata_blob("v"), expiration()).await.unwrap();
    assert_eq!(result, MetadataPersistResult::RetryNeeded);
}
