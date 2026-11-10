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

mod lock {
    use std::{
        sync::Arc,
        time::{Duration, SystemTime},
    };

    use external_db_client::{
        DataBlobHandler, ExternalDbClient, MetadataBlobRead, MetadataPersistResult,
    };
    use private_memory_test_database_server_lib::service::{self, CLOCK_SKEW_MARGIN, LockState};
    use sealed_memory_rust_proto::oak::private_memory::{
        AcquireUnencryptedDataBlobLockRequest, DataBlob, EncryptedDataBlob, EncryptedMetadataBlob,
        WriteUnencryptedDataBlobRequest,
    };
    use tokio::net::TcpListener;
    use tonic::{Code, transport::Channel};

    const UID: &str = "test_uid";
    const EXPIRATION: prost_types::Timestamp =
        prost_types::Timestamp { seconds: 1893456000, nanos: 0 };
    const LEASE: Duration = Duration::from_secs(30);

    async fn start() -> (ExternalDbClient, Arc<LockState>) {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let lock_state = LockState::new();
        let server_lock_state = lock_state.clone();
        tokio::spawn(async move {
            service::create_with_lock_state(listener, server_lock_state).await.unwrap();
        });
        let channel =
            Channel::from_shared(format!("http://{addr}")).unwrap().connect().await.unwrap();
        (ExternalDbClient::new(channel), lock_state)
    }

    async fn start_registered() -> (ExternalDbClient, Arc<LockState>) {
        let (mut client, lock_state) = start().await;
        client
            .add_unencrypted_blob(unencrypted_blob(b"wrapped-dek-v1"), None)
            .await
            .expect("registration write failed");
        (client, lock_state)
    }

    fn unencrypted_blob(contents: &[u8]) -> DataBlob {
        DataBlob { id: UID.to_string(), blob: contents.to_vec() }
    }

    fn metadata_blob(data: Vec<u8>, version: &str) -> EncryptedMetadataBlob {
        EncryptedMetadataBlob {
            encrypted_data_blob: Some(EncryptedDataBlob { nonce: vec![1, 2, 3], data }),
            version: version.to_string(),
        }
    }

    fn status_code(error: &anyhow::Error) -> Code {
        error.downcast_ref::<tonic::Status>().expect("expected a tonic::Status").code()
    }

    fn assert_expires_in(
        lock_expire_time: Option<prost_types::Timestamp>,
        lock_state: &LockState,
        expected: Duration,
    ) {
        let expire_time =
            SystemTime::try_from(lock_expire_time.expect("lock_expire_time missing")).unwrap();
        assert_eq!(expire_time, lock_state.now() + expected);
    }

    async fn read_unencrypted(client: &mut ExternalDbClient) -> Vec<u8> {
        client.get_unencrypted_blob(&UID.to_string(), true).await.unwrap().unwrap().blob
    }

    // acquire_unencrypted_blob_lock

    #[tokio::test]
    async fn acquire_returns_token_and_expiry() {
        let (mut client, lock_state) = start_registered().await;

        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        assert!(!lock.lock_token.is_empty());
        assert_expires_in(lock.lock_expire_time, &lock_state, LEASE);
        assert_eq!(lock_state.held_token(UID).await, Some(lock.lock_token));
    }

    #[tokio::test]
    async fn acquire_missing_row_is_not_found_error() {
        let (mut client, _) = start().await;

        let error =
            client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap_err();

        assert_eq!(status_code(&error), Code::NotFound);
    }

    #[tokio::test]
    async fn acquire_zero_duration_uses_default() {
        let (mut client, lock_state) = start_registered().await;

        let lock =
            client.acquire_unencrypted_blob_lock(&UID.to_string(), Duration::ZERO).await.unwrap();

        assert_expires_in(lock.lock_expire_time, &lock_state, Duration::from_secs(60));
    }

    #[tokio::test]
    async fn acquire_duration_is_capped_at_ten_minutes() {
        let (mut client, lock_state) = start_registered().await;

        let lock = client
            .acquire_unencrypted_blob_lock(&UID.to_string(), Duration::from_secs(3600))
            .await
            .unwrap();

        assert_expires_in(lock.lock_expire_time, &lock_state, Duration::from_secs(600));
    }

    #[tokio::test]
    async fn acquire_already_locked_row_is_aborted() {
        let (mut client, _) = start_registered().await;
        let first = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let error =
            client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap_err();

        assert_eq!(status_code(&error), Code::Aborted);
        // The failed attempt did not disturb the first lock.
        client
            .extend_unencrypted_blob_lock(&UID.to_string(), &first.lock_token, LEASE)
            .await
            .unwrap();
    }

    #[tokio::test]
    async fn row_can_be_reacquired_only_after_the_clock_skew_margin() {
        let (mut client, lock_state) = start_registered().await;
        let first = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        // Just before expiry the row is still taken.
        lock_state.advance(LEASE - Duration::from_secs(1));
        let error =
            client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap_err();
        assert_eq!(status_code(&error), Code::Aborted);

        // The host keeps an expired lease closed to everybody else for
        // another CLOCK_SKEW_MARGIN, in case its clock runs ahead of the
        // holder's.
        lock_state.advance(Duration::from_secs(2));
        let error =
            client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap_err();
        assert_eq!(status_code(&error), Code::Aborted);

        // After that, anyone can take the row, with a new token.
        lock_state.advance(CLOCK_SKEW_MARGIN);
        let second = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();
        assert_ne!(first.lock_token, second.lock_token);
    }

    #[tokio::test]
    async fn acquire_negative_duration_is_invalid_argument_error() {
        // Not reachable through the client, which takes a std Duration, so
        // this goes straight to the RPC.
        let (mut client, _) = start_registered().await;

        let status = client
            .acquire_unencrypted_data_blob_lock(AcquireUnencryptedDataBlobLockRequest {
                id: UID.to_string(),
                lock_duration: Some(prost_types::Duration { seconds: -1, nanos: 0 }),
            })
            .await
            .unwrap_err();

        assert_eq!(status.code(), Code::InvalidArgument);
    }

    // extend_unencrypted_blob_lock

    #[tokio::test]
    async fn extend_replaces_expiry_relative_to_now() {
        let (mut client, lock_state) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        // Shorter than the time left: the expiry moves earlier, showing the
        // new duration replaces the old expiry rather than adding to it.
        let extended = client
            .extend_unencrypted_blob_lock(
                &UID.to_string(),
                &lock.lock_token,
                Duration::from_secs(10),
            )
            .await
            .unwrap();

        assert_expires_in(extended.lock_expire_time, &lock_state, Duration::from_secs(10));
    }

    #[tokio::test]
    async fn extend_keeps_lock_alive_past_original_lease() {
        let (mut client, lock_state) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        // At t=20s, extend by 30s: the lease now ends at t=50s instead of 30s.
        lock_state.advance(Duration::from_secs(20));
        client
            .extend_unencrypted_blob_lock(&UID.to_string(), &lock.lock_token, LEASE)
            .await
            .unwrap();

        // At t=40s, past the original expiry, the row is still ours.
        lock_state.advance(Duration::from_secs(20));
        let error =
            client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap_err();
        assert_eq!(status_code(&error), Code::Aborted);

        // At t=50s, the extended expiry, the lease is over; once the clock
        // skew margin has passed too, the row is free again.
        lock_state.advance(Duration::from_secs(10) + CLOCK_SKEW_MARGIN);
        client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();
    }

    #[tokio::test]
    async fn extend_with_wrong_token_is_aborted() {
        let (mut client, _) = start_registered().await;
        client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let error = client
            .extend_unencrypted_blob_lock(&UID.to_string(), "not-the-token", LEASE)
            .await
            .unwrap_err();

        assert_eq!(status_code(&error), Code::Aborted);
    }

    #[tokio::test]
    async fn extend_expired_lock_is_aborted() {
        let (mut client, lock_state) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();
        lock_state.advance(LEASE);

        let error = client
            .extend_unencrypted_blob_lock(&UID.to_string(), &lock.lock_token, LEASE)
            .await
            .unwrap_err();

        assert_eq!(status_code(&error), Code::Aborted);
    }

    #[tokio::test]
    async fn extend_unlocked_row_is_aborted() {
        let (mut client, _) = start_registered().await;

        let error = client
            .extend_unencrypted_blob_lock(&UID.to_string(), "some-token", LEASE)
            .await
            .unwrap_err();

        assert_eq!(status_code(&error), Code::Aborted);
    }

    #[tokio::test]
    async fn extend_with_empty_token_is_invalid_argument_error() {
        let (mut client, _) = start_registered().await;
        client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let error =
            client.extend_unencrypted_blob_lock(&UID.to_string(), "", LEASE).await.unwrap_err();

        assert_eq!(status_code(&error), Code::InvalidArgument);
    }

    // release_unencrypted_blob_lock

    #[tokio::test]
    async fn release_with_empty_token_is_invalid_argument_error() {
        let (mut client, lock_state) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let error = client.release_unencrypted_blob_lock(&UID.to_string(), "").await.unwrap_err();

        assert_eq!(status_code(&error), Code::InvalidArgument);
        assert_eq!(lock_state.held_token(UID).await, Some(lock.lock_token));
    }

    #[tokio::test]
    async fn release_frees_the_row() {
        let (mut client, lock_state) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        client.release_unencrypted_blob_lock(&UID.to_string(), &lock.lock_token).await.unwrap();

        assert_eq!(lock_state.held_token(UID).await, None);
        client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();
    }

    #[tokio::test]
    async fn release_expired_lock_succeeds() {
        let (mut client, lock_state) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();
        lock_state.advance(LEASE);

        client.release_unencrypted_blob_lock(&UID.to_string(), &lock.lock_token).await.unwrap();
    }

    #[tokio::test]
    async fn release_twice_succeeds() {
        let (mut client, _) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        client.release_unencrypted_blob_lock(&UID.to_string(), &lock.lock_token).await.unwrap();
        client.release_unencrypted_blob_lock(&UID.to_string(), &lock.lock_token).await.unwrap();
    }

    #[tokio::test]
    async fn release_with_wrong_token_is_aborted_and_keeps_lock() {
        let (mut client, lock_state) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let error = client
            .release_unencrypted_blob_lock(&UID.to_string(), "not-the-token")
            .await
            .unwrap_err();

        assert_eq!(status_code(&error), Code::Aborted);
        assert_eq!(lock_state.held_token(UID).await, Some(lock.lock_token));
    }

    // Lock-gated writes

    #[tokio::test]
    async fn unencrypted_write_is_aborted_while_row_is_locked() {
        let (mut client, lock_state) = start_registered().await;
        lock_state.lock(UID).await;

        let error = client
            .add_unencrypted_blob(unencrypted_blob(b"wrapped-dek-v2"), None)
            .await
            .unwrap_err();

        assert_eq!(status_code(&error), Code::Aborted);
        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v1");
    }

    #[tokio::test]
    async fn untokened_write_is_fenced_for_the_clock_skew_margin_then_insert_only() {
        let (mut client, lock_state) = start_registered().await;
        client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        lock_state.advance(LEASE + Duration::from_secs(1));
        let error = client
            .add_unencrypted_blob(unencrypted_blob(b"wrapped-dek-v2"), None)
            .await
            .unwrap_err();
        assert_eq!(status_code(&error), Code::Aborted);

        lock_state.advance(CLOCK_SKEW_MARGIN);
        let error = client
            .add_unencrypted_blob(unencrypted_blob(b"wrapped-dek-v2"), None)
            .await
            .unwrap_err();
        assert_eq!(status_code(&error), Code::AlreadyExists);
        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v1");
    }

    #[tokio::test]
    async fn tokened_unencrypted_write_overwrites_the_row() {
        let (mut client, _) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        client
            .write_unencrypted_data_blob(WriteUnencryptedDataBlobRequest {
                data_blob: Some(unencrypted_blob(b"wrapped-dek-v2")),
                lock_token: lock.lock_token,
            })
            .await
            .unwrap();

        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v2");
    }

    #[tokio::test]
    async fn unencrypted_write_with_wrong_token_is_aborted() {
        let (mut client, _) = start_registered().await;
        client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let status = client
            .write_unencrypted_data_blob(WriteUnencryptedDataBlobRequest {
                data_blob: Some(unencrypted_blob(b"wrapped-dek-v2")),
                lock_token: "not-the-lock-token".to_string(),
            })
            .await
            .unwrap_err();

        assert_eq!(status.code(), Code::Aborted);
        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v1");
    }

    #[tokio::test]
    async fn tokened_write_to_missing_row_succeeds() {
        // Locks are only granted on existing rows, so there is nothing to
        // fence off; the host lets the write through whatever the token.
        let (mut client, lock_state) = start().await;

        let result = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![1], ""),
                EXPIRATION,
                "some-token",
                None,
            )
            .await
            .unwrap();

        assert!(
            matches!(result, MetadataPersistResult::Succeeded { committed_version: Some(_) }),
            "{result:?}"
        );
        assert_eq!(lock_state.rejections(), 0);
    }

    #[tokio::test]
    async fn metadata_write_without_token_while_locked_is_lock_conflict() {
        let (mut client, lock_state) = start_registered().await;
        lock_state.lock(UID).await;

        let result = client
            .add_metadata_blob_stream(&UID.to_string(), &metadata_blob(vec![1], ""), EXPIRATION)
            .await
            .unwrap();

        assert_eq!(result, MetadataPersistResult::LockConflict);
        assert_eq!(lock_state.rejections(), 1);
    }

    #[tokio::test]
    async fn metadata_write_with_holders_token_succeeds() {
        let (mut client, _) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let result = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![1], ""),
                EXPIRATION,
                &lock.lock_token,
                None,
            )
            .await
            .unwrap();

        assert!(
            matches!(result, MetadataPersistResult::Succeeded { committed_version: Some(_) }),
            "{result:?}"
        );
    }

    #[tokio::test]
    async fn metadata_write_with_wrong_token_is_lock_conflict() {
        let (mut client, _) = start_registered().await;
        client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let result = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![1], ""),
                EXPIRATION,
                "not-the-token",
                None,
            )
            .await
            .unwrap();

        assert_eq!(result, MetadataPersistResult::LockConflict);
    }

    #[tokio::test]
    async fn metadata_write_with_released_token_is_lock_conflict() {
        // A caller whose lock is gone must not be able to write with it, even
        // though the row is now unlocked.
        let (mut client, _) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();
        client.release_unencrypted_blob_lock(&UID.to_string(), &lock.lock_token).await.unwrap();

        let result = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![1], ""),
                EXPIRATION,
                &lock.lock_token,
                None,
            )
            .await
            .unwrap();

        assert_eq!(result, MetadataPersistResult::LockConflict);
    }

    #[tokio::test]
    async fn metadata_write_with_expired_token_is_lock_conflict() {
        let (mut client, lock_state) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();
        lock_state.advance(LEASE);

        let result = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![1], ""),
                EXPIRATION,
                &lock.lock_token,
                None,
            )
            .await
            .unwrap();

        assert_eq!(result, MetadataPersistResult::LockConflict);
    }

    #[tokio::test]
    async fn multi_chunk_metadata_write_carries_token() {
        // Larger than one 1MB chunk, so the token has to travel on the first
        // message of a multi-message stream.
        let (mut client, _) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();
        let data = vec![0x42u8; 5 * 1024 * 1024 / 2];

        let result = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(data.clone(), ""),
                EXPIRATION,
                &lock.lock_token,
                Some(unencrypted_blob(b"wrapped-dek-v2")),
            )
            .await
            .unwrap();

        assert!(
            matches!(result, MetadataPersistResult::Succeeded { committed_version: Some(_) }),
            "{result:?}"
        );
        let MetadataBlobRead::Blob(stored) =
            client.get_metadata_blob_stream(&UID.to_string(), EXPIRATION, None).await.unwrap()
        else {
            panic!("metadata blob missing");
        };
        assert_eq!(stored.encrypted_data_blob.unwrap().data, data);
        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v2");
    }

    // Atomic metadata + unencrypted blob writes

    #[tokio::test]
    async fn metadata_write_with_unencrypted_blob_writes_both() {
        let (mut client, _) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let result = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![7, 7, 7], ""),
                EXPIRATION,
                &lock.lock_token,
                Some(unencrypted_blob(b"wrapped-dek-v2")),
            )
            .await
            .unwrap();

        assert!(
            matches!(result, MetadataPersistResult::Succeeded { committed_version: Some(_) }),
            "{result:?}"
        );
        let MetadataBlobRead::Blob(stored) =
            client.get_metadata_blob_stream(&UID.to_string(), EXPIRATION, None).await.unwrap()
        else {
            panic!("metadata blob missing");
        };
        assert_eq!(stored.encrypted_data_blob.unwrap().data, vec![7, 7, 7]);
        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v2");
    }

    #[tokio::test]
    async fn metadata_write_without_unencrypted_blob_leaves_it_untouched() {
        let (mut client, _) = start_registered().await;
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![1], ""),
                EXPIRATION,
                &lock.lock_token,
                None,
            )
            .await
            .unwrap();

        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v1");
    }

    #[tokio::test]
    async fn version_conflict_does_not_write_unencrypted_blob() {
        let (mut client, _) = start_registered().await;
        client
            .add_metadata_blob_stream(&UID.to_string(), &metadata_blob(vec![1], ""), EXPIRATION)
            .await
            .unwrap();
        let lock = client.acquire_unencrypted_blob_lock(&UID.to_string(), LEASE).await.unwrap();

        let result = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![2], "stale-version"),
                EXPIRATION,
                &lock.lock_token,
                Some(unencrypted_blob(b"wrapped-dek-v2")),
            )
            .await
            .unwrap();

        assert_eq!(result, MetadataPersistResult::RetryNeeded);
        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v1");
    }

    #[tokio::test]
    async fn lock_conflict_does_not_write_unencrypted_blob() {
        let (mut client, lock_state) = start_registered().await;
        lock_state.lock(UID).await;

        let result = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![1], ""),
                EXPIRATION,
                "",
                Some(unencrypted_blob(b"wrapped-dek-v2")),
            )
            .await
            .unwrap();

        assert_eq!(result, MetadataPersistResult::LockConflict);
        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v1");
    }

    #[tokio::test]
    async fn unencrypted_blob_with_mismatched_id_is_invalid_argument() {
        let (mut client, _) = start_registered().await;

        let error = client
            .add_metadata_blob_stream_with_lock(
                &UID.to_string(),
                &metadata_blob(vec![1], ""),
                EXPIRATION,
                "",
                Some(DataBlob { id: "other_uid".to_string(), blob: b"wrapped-dek-v2".to_vec() }),
            )
            .await
            .unwrap_err();

        assert_eq!(status_code(&error), Code::InvalidArgument);
        assert_eq!(read_unencrypted(&mut client).await, b"wrapped-dek-v1");
    }
}
