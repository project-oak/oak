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

use external_db_client::{DataBlobHandler, ExternalDbClient};
use sealed_memory_rust_proto::oak::private_memory::{EncryptedDataBlob, EncryptedMetadataBlob};
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
    let result = client.add_metadata_blob_stream(&id, metadata_blob.clone()).await.unwrap();
    assert_eq!(result, external_db_client::MetadataPersistResult::Succeeded);

    // Test get_metadata_blob_stream
    let retrieved = client.get_metadata_blob_stream(&id).await.unwrap();
    assert!(retrieved.is_some());
    let retrieved = retrieved.unwrap();
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

    let retrieved = client.get_metadata_blob_stream(&"non_existent".to_string()).await.unwrap();
    assert!(retrieved.is_none());
}
