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

use std::{
    collections::HashSet,
    time::{Duration, SystemTime},
};

use attestation_testing::{
    DUMMY_ATTESTATION_ID, DummySessionBindingVerifierProvider, RejectingVerifier,
    dummy_client_session_config,
};
use client::{PrivateMemoryAppClient, PrivateMemoryClient};
use oak_session::{attestation::AttestationType, config::SessionConfig, handshake::HandshakeType};
use private_memory_test_utils::{start_server, start_server_with_config, system_time_to_timestamp};
use sealed_memory_rust_proto::{
    oak::private_memory::{LlmView, LlmViews, MemorySource},
    prelude::v1::*,
};

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

#[tokio::test(flavor = "multi_thread")]
async fn test_client() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();
    let llm_view = LlmViews {
        llm_views: vec![LlmView {
            embedding: Some(Embedding {
                model_signature: "test_model".to_string(),
                values: vec![1.0, 0.0, 0.0],
            }),
            ..Default::default()
        }],
    };
    let memory_to_add = Memory {
        id: "".to_string(),
        tags: vec!["test_tag".to_string()],
        views: Some(llm_view),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let response = client.add_memory(memory_to_add).await.unwrap();
    let memory_id = response.id;

    let response = client.get_memory_by_id(&memory_id, None).await.unwrap();
    assert!(response.success);
    assert_eq!(response.memory.unwrap().id, memory_id);
}

/// Verifies that the dummy attested handshake (SelfUnidirectional server +
/// PeerUnidirectional client) completes successfully.
#[tokio::test(flavor = "multi_thread")]
async fn test_client_with_dummy_attestation() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_dummy_attested_user";

    let mut client = PrivateMemoryClient::create_with_start_session_config(
        &url,
        pm_uid,
        TEST_EK,
        dummy_client_session_config(),
    )
    .await
    .unwrap();

    let memory_to_add = Memory {
        id: "".to_string(),
        tags: vec!["test_tag".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let response = client.add_memory(memory_to_add).await.unwrap();
    let memory_id = response.id;

    let response = client.get_memory_by_id(&memory_id, None).await.unwrap();
    assert!(response.success);
    assert_eq!(response.memory.unwrap().id, memory_id);
}

/// Verifies that the client aborts when attestation evidence fails
/// verification.
#[tokio::test(flavor = "multi_thread")]
async fn test_client_rejects_bad_evidence() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_reject_user";

    let rejecting_config =
        SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN)
            .add_peer_verifier_with_binding_verifier_provider(
                DUMMY_ATTESTATION_ID.to_string(),
                Box::new(RejectingVerifier),
                Box::new(DummySessionBindingVerifierProvider),
            )
            .build();

    let result = PrivateMemoryClient::create_with_start_session_config(
        &url,
        pm_uid,
        TEST_EK,
        rejecting_config,
    )
    .await;

    assert!(result.is_err(), "client should fail when evidence is rejected");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_client_pagination() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_pagination_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let tag = "pagination_tag";
    let mut expected_ids = HashSet::new();
    for _ in 0..50 {
        let memory_to_add = Memory {
            id: "".to_string(),
            tags: vec![tag.to_string()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    embedding: Some(Embedding {
                        model_signature: "test_model".to_string(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        };
        let response = client.add_memory(memory_to_add).await.unwrap();
        expected_ids.insert(response.id);
    }

    // Test GetMemories pagination
    let mut actual_ids = HashSet::new();
    let mut next_page_token = "".to_string();
    for i in 0..10 {
        let response = client.get_memories(tag, 5, None, &next_page_token).await.unwrap();
        assert_eq!(response.memories.len(), 5);
        for memory in response.memories {
            actual_ids.insert(memory.id);
        }
        next_page_token = response.next_page_token;
        if i < 9 {
            assert!(!next_page_token.is_empty());
        }
    }
    assert!(next_page_token.is_empty());
    assert_eq!(expected_ids, actual_ids);
}

#[tokio::test(flavor = "multi_thread")]
async fn test_client_keysync_invalid_key() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_keysync_invalid_key_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let invalid_kek: &[u8; 32] = b"invalidkekinvalidkekinvalidkek_k";
    let status = client.key_sync(pm_uid, invalid_kek).await;
    assert_eq!(status.unwrap(), key_sync_response::Status::InvalidKey);
}

#[tokio::test(flavor = "multi_thread")]
async fn test_get_by_id_with_expired_memories() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_expired_memory_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    // Add memory that will expire in 2 seconds
    let expired_memory_to_add = Memory {
        id: "".to_string(),
        tags: vec!["expired".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(2),
        )),
        ..Default::default()
    };

    // Add memory that will expire in 60 seconds
    let non_expired_memory_to_add = Memory {
        id: "".to_string(),
        tags: vec!["non_expired".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(60),
        )),
        ..Default::default()
    };

    let expired_memory_id = client.add_memory(expired_memory_to_add).await.unwrap().id;
    let non_expired_memory_id = client.add_memory(non_expired_memory_to_add).await.unwrap().id;

    // Sleep 3 seconds in real time to let `expired_memory` actually expire
    tokio::time::sleep(Duration::from_secs(3)).await;

    // Try to retrieve the expired memory: should not be found
    let get_response_expired = client.get_memory_by_id(&expired_memory_id, None).await.unwrap();
    assert!(!get_response_expired.success);
    assert!(get_response_expired.memory.is_none());

    // Try to retrieve the non-expired memory: should be found
    let get_response_non_expired =
        client.get_memory_by_id(&non_expired_memory_id, None).await.unwrap();
    assert!(get_response_non_expired.success);
    assert_eq!(get_response_non_expired.memory.unwrap().id, non_expired_memory_id);

    // Add a memory with no expiration - should fail and close the stream
    let no_expiration_memory_to_add = Memory {
        id: "".to_string(),
        tags: vec!["no_expiration".to_string()],
        expiration_timestamp: None,
        ..Default::default()
    };
    let response_no_expiration = client.add_memory(no_expiration_memory_to_add).await;
    assert!(response_no_expiration.is_err());
}

#[tokio::test(flavor = "multi_thread")]
async fn test_get_by_tag_with_expired_memories() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_expired_memory_by_tag_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let tag = "test_expiration_tag";
    // Add memory that will expire in 2 seconds
    let expired_memory_to_add = Memory {
        id: "".to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(2),
        )),
        ..Default::default()
    };

    // Add memory that will expire in 60 seconds
    let non_expired_memory_to_add = Memory {
        id: "".to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(60),
        )),
        ..Default::default()
    };

    let expired_memory_id = client.add_memory(expired_memory_to_add).await.unwrap().id;
    let non_expired_memory_id = client.add_memory(non_expired_memory_to_add).await.unwrap().id;

    // Sleep 3 seconds in real time to let `expired_memory` actually expire
    tokio::time::sleep(Duration::from_secs(3)).await;

    // Retrieve memories by tag
    let response = client.get_memories(tag, 10, None, "").await.unwrap();

    // Check that only non-expired memories are returned
    assert_eq!(response.memories.len(), 1);
    let returned_ids: HashSet<String> = response.memories.into_iter().map(|m| m.id).collect();
    assert!(returned_ids.contains(&non_expired_memory_id));
    assert!(!returned_ids.contains(&expired_memory_id));

    // Retrieve memories with the empty tag
    let response = client.get_memories("", 10, None, "").await.unwrap();

    // Check that only non-expired memories are returned
    assert_eq!(response.memories.len(), 1);
    let returned_ids: HashSet<String> = response.memories.into_iter().map(|m| m.id).collect();
    assert!(returned_ids.contains(&non_expired_memory_id));
    assert!(!returned_ids.contains(&expired_memory_id));

    // Add a memory with no expiration - should fail and close the stream
    let no_expiration_memory_to_add = Memory {
        id: "".to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: None,
        ..Default::default()
    };
    let add_no_exp_res = client.add_memory(no_expiration_memory_to_add).await;
    assert!(add_no_exp_res.is_err());
}

#[tokio::test(flavor = "multi_thread")]
async fn test_get_memories_by_id() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_get_memories_by_id_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    // Add three memories
    let memory1 = Memory {
        id: "".to_string(),
        tags: vec!["tag1".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    let memory2 = Memory {
        id: "".to_string(),
        tags: vec!["tag2".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    let memory3 = Memory {
        id: "".to_string(),
        tags: vec!["tag3".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let id1 = client.add_memory(memory1).await.unwrap().id;
    let id2 = client.add_memory(memory2).await.unwrap().id;
    let id3 = client.add_memory(memory3).await.unwrap().id;

    // Test fetching multiple memories by ID
    let response =
        client.get_memories_by_id(vec![id3.clone(), id1.clone(), id2.clone()], None).await.unwrap();

    assert_eq!(response.memories.len(), 3);
    assert!(response.not_found_ids.is_empty());
    let returned_ids: HashSet<String> = response.memories.iter().map(|m| m.id.clone()).collect();
    assert!(returned_ids.contains(&id1));
    assert!(returned_ids.contains(&id2));
    assert!(returned_ids.contains(&id3));

    // Test fetching a single memory by ID
    let response = client.get_memories_by_id(vec![id2.clone()], None).await.unwrap();
    assert_eq!(response.memories.len(), 1);
    assert_eq!(response.memories[0].id, id2);
    assert!(response.not_found_ids.is_empty());

    // Test fetching with a non-existent ID - should return found ones and report
    // not found
    let response = client
        .get_memories_by_id(
            vec![
                id1.clone(),
                "non_existent_id".to_string(),
                id3.clone(),
                "another_missing".to_string(),
            ],
            None,
        )
        .await
        .unwrap();
    assert_eq!(response.memories.len(), 2);
    let returned_ids: HashSet<String> = response.memories.iter().map(|m| m.id.clone()).collect();
    assert!(returned_ids.contains(&id1));
    assert!(returned_ids.contains(&id3));
    assert_eq!(response.not_found_ids.len(), 2);
    assert!(response.not_found_ids.contains(&"non_existent_id".to_string()));
    assert!(response.not_found_ids.contains(&"another_missing".to_string()));

    // Test with all non-existent IDs
    let response = client
        .get_memories_by_id(vec!["missing1".to_string(), "missing2".to_string()], None)
        .await
        .unwrap();
    assert!(response.memories.is_empty());
    assert_eq!(response.not_found_ids.len(), 2);
}

/// Every application error comes back inside `SealedMemoryResponse.error` as
/// a `google.rpc.Status`, with the gRPC stream left open. There is no longer
/// a header or config knob to opt out of this.
#[tokio::test(flavor = "multi_thread")]
async fn test_error_propagation_behavior() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_error_user";

    let mut client = PrivateMemoryClient::create_with_start_session_config(
        &url,
        pm_uid,
        TEST_EK,
        dummy_client_session_config(),
    )
    .await
    .unwrap();

    // Send an invalid request (empty key) to trigger an error.
    let request = UserRegistrationRequest {
        pm_uid: pm_uid.to_string(),
        key_encryption_key: vec![], // Invalid!
        ..Default::default()
    };

    let response = client
        .invoke(sealed_memory_request::Request::UserRegistrationRequest(request.clone()))
        .await
        .unwrap();

    match response {
        sealed_memory_response::Response::Error(status) => {
            assert_eq!(status.code, tonic::Code::InvalidArgument as i32);
            assert!(status.message.contains("key_encryption_key not set"));
        }
        _ => panic!("expected error response, got {:?}", response),
    }

    // The session survives the error, so a subsequent request still works.
    let response = client
        .invoke(sealed_memory_request::Request::UserRegistrationRequest(UserRegistrationRequest {
            pm_uid: pm_uid.to_string(),
            key_encryption_key: TEST_EK.to_vec(),
            boot_strap_info: Some(Default::default()),
        }))
        .await
        .unwrap();
    assert!(
        matches!(response, sealed_memory_response::Response::UserRegistrationResponse(_)),
        "expected the session to stay usable, got {:?}",
        response
    );

    // The typed helpers unwrap the `error` arm, so callers see the server's
    // message rather than a generic type mismatch.
    let err = client.add_memory(Memory::default()).await.unwrap_err();
    assert!(
        !format!("{err:?}").contains("unexpected response type"),
        "typed helper should surface the server error, got: {err:?}"
    );
}

// ── Memory source allowlist tests ──────────────────────────────────────────

fn config_with_memory_source_allowlist(
    db_addr: std::net::SocketAddr,
) -> private_memory_server_lib::app::ApplicationConfig {
    let mut config = private_memory_test_utils::default_test_application_config(db_addr);
    config.allowed_memory_sources = vec!["source_a".to_string(), "source_b".to_string()];
    config
}

fn create_memory_with_source(_id: &str, source_id: &str) -> Memory {
    Memory {
        id: "".to_string(),
        source: Some(MemorySource { source_id: source_id.to_string() }),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_memory_source_allowlist_accepted() {
    let (addr, _server, _db, _persist) =
        start_server_with_config(config_with_memory_source_allowlist, None).await.unwrap();
    let url = format!("http://{}", addr);
    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, "source_ok_user", TEST_EK)
            .await
            .unwrap();

    let memory = create_memory_with_source("mem_allowed", "source_a");
    client.add_memory(memory).await.expect("allowed source should succeed");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_memory_source_allowlist_rejected() {
    let (addr, _server, _db, _persist) =
        start_server_with_config(config_with_memory_source_allowlist, None).await.unwrap();
    let url = format!("http://{}", addr);
    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, "source_reject_user", TEST_EK)
            .await
            .unwrap();

    let memory = create_memory_with_source("mem_bad", "unknown_source");
    let result = client.add_memory(memory).await;
    assert!(result.is_err(), "unlisted source should be rejected");
    let err = result.unwrap_err();
    assert!(
        format!("{:?}", err).contains("not in the allowed sources list"),
        "error should mention allowlist, got: {err:?}"
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn test_memory_source_allowlist_missing_source() {
    let (addr, _server, _db, _persist) =
        start_server_with_config(config_with_memory_source_allowlist, None).await.unwrap();
    let url = format!("http://{}", addr);
    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, "source_missing_user", TEST_EK)
            .await
            .unwrap();

    let memory = Memory {
        id: "".to_string(),
        source: None,
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    let result = client.add_memory(memory).await;
    assert!(result.is_err(), "missing source should be rejected");
    let err = result.unwrap_err();
    assert!(
        format!("{:?}", err).contains("source is required"),
        "error should mention required source, got: {err:?}"
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn test_memory_source_allowlist_empty_source_id() {
    let (addr, _server, _db, _persist) =
        start_server_with_config(config_with_memory_source_allowlist, None).await.unwrap();
    let url = format!("http://{}", addr);
    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, "source_empty_user", TEST_EK)
            .await
            .unwrap();

    let memory = create_memory_with_source("mem_empty_src", "");
    let result = client.add_memory(memory).await;
    assert!(result.is_err(), "empty source_id should be rejected");
    let err = result.unwrap_err();
    assert!(
        format!("{:?}", err).contains("source_id must not be empty"),
        "error should mention empty source_id, got: {err:?}"
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn test_memory_source_no_allowlist_accepts_any() {
    // Default config has empty allowlist, so any source should be accepted.
    let (addr, _server, _db, _persist) = start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, "source_any_user", TEST_EK)
            .await
            .unwrap();

    // Memory with a source should be fine.
    let memory_with = create_memory_with_source("mem_with_src", "anything");
    client.add_memory(memory_with).await.expect("any source accepted without allowlist");

    // Memory without a source should also be fine.
    let memory_without = Memory {
        id: "".to_string(),
        source: None,
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    client.add_memory(memory_without).await.expect("no source accepted without allowlist");
}

/// Verifies the Invoke RPC path: handshake, key sync, add multiple
/// memories, retrieve them all.
#[tokio::test(flavor = "multi_thread")]
async fn test_invoke_basic() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_invoke_concurrent_user";

    let mut client = PrivateMemoryClient::create_with_invoke(&url, pm_uid, TEST_EK).await.unwrap();

    // Add multiple memories through the concurrent dispatch loop.
    let num_memories = 10;
    let mut memory_ids = Vec::new();
    for _ in 0..num_memories {
        let memory = Memory {
            id: "".to_string(),
            tags: vec!["invoke_test".to_string()],
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        };
        let response = client.add_memory(memory).await.unwrap();
        memory_ids.push(response.id);
    }

    // Read them all back to verify correctness.
    for memory_id in &memory_ids {
        let response = client.get_memory_by_id(memory_id, None).await.unwrap();
        assert!(response.success, "memory {memory_id} should exist");
        assert_eq!(response.memory.unwrap().id, *memory_id);
    }

    // Batch fetch all by id.
    let response = client.get_memories_by_id(memory_ids.clone(), None).await.unwrap();
    assert_eq!(response.memories.len(), num_memories);
    assert!(response.not_found_ids.is_empty());
}

/// Load test: compares wall-clock time for sequential Invoke dispatch vs
/// pipelined InvokeAsync dispatch on a single stream. With 150ms simulated DB
/// latency per blob read, pipelined dispatch should be significantly faster
/// because the server processes requests concurrently via FuturesOrdered.
#[tokio::test(flavor = "multi_thread")]
async fn test_invoke_async_pipelining_speedup() {
    use client::AsyncPrivateMemoryClient;

    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let num_requests: usize = 10;
    let pm_uid = "load_test_user";

    // --- Sequential baseline: Invoke RPC, send-then-receive one at a time ---
    let mut seq_client =
        PrivateMemoryClient::create_with_invoke(&url, pm_uid, TEST_EK).await.unwrap();

    // Seed memories via the sequential Invoke client.
    let mut seq_ids = Vec::new();
    for _ in 0..num_requests {
        let memory = Memory {
            id: "".to_string(),
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        };
        seq_ids.push(seq_client.add_memory(memory).await.unwrap().id);
    }

    let seq_start = std::time::Instant::now();
    for id in &seq_ids {
        seq_client.get_memory_by_id(id, None).await.unwrap();
    }
    let seq_elapsed = seq_start.elapsed();

    // --- Pipelined: InvokeAsync RPC on a single stream ---
    // Seed memories via the async client (so they exist in this session's DB).
    let mut async_client = AsyncPrivateMemoryClient::create(&url, pm_uid, TEST_EK).await.unwrap();
    let mut pipe_ids = Vec::new();
    for _ in 0..num_requests {
        let memory = Memory {
            id: "".to_string(),
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        };
        pipe_ids.push(async_client.add_memory(memory).await.unwrap().id);
    }

    let pipe_start = std::time::Instant::now();
    // Send all requests without waiting for responses.
    for id in &pipe_ids {
        let request = sealed_memory_request::Request::GetMemoryByIdRequest(GetMemoryByIdRequest {
            id: id.clone(),
            result_mask: None,
        });
        async_client.send_request(request).await.unwrap();
    }
    // Collect all responses.
    for _i in 0..num_requests {
        let response = async_client.receive_response().await.unwrap();
        match response {
            sealed_memory_response::Response::GetMemoryByIdResponse(resp) => {
                assert!(resp.success, "memory should exist: {:?}", resp);
            }
            other => panic!("unexpected response type: {other:?}"),
        }
    }
    let pipe_elapsed = pipe_start.elapsed();

    let speedup = seq_elapsed.as_millis() as f64 / pipe_elapsed.as_millis() as f64;
    eprintln!("=== InvokeAsync Pipelining Load Test ===");
    eprintln!("  Requests:    {num_requests}");
    eprintln!("  Sequential (Invoke):      {:?}", seq_elapsed);
    eprintln!("  Pipelined  (InvokeAsync): {:?}", pipe_elapsed);
    eprintln!("  Speedup:     {speedup:.2}x");

    // With 150ms DB latency and 10 requests, pipelining should show
    // significant speedup (requests overlap on the server).
    assert!(speedup > 1.5, "Expected pipelining speedup > 1.5x, got {speedup:.2}x");
}

fn make_test_memory(_id: &str, tag: &str) -> Memory {
    Memory {
        id: "".to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    }
}

fn make_named_test_memory(_id: &str, name: &str, tag: &str) -> Memory {
    Memory {
        id: "".to_string(),
        name: name.to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    }
}

/// Test that batch add_memories successfully adds multiple memories.
#[tokio::test(flavor = "multi_thread")]
async fn test_add_memories_basic() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_add_memories_basic_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let memories = vec![make_test_memory("mem_1", "tag_a"), make_test_memory("mem_2", "tag_a")];

    let response = client.add_memories(memories).await.unwrap();
    assert_eq!(response.results.len(), 2);

    // Both should succeed with their IDs.
    for (i, result) in response.results.iter().enumerate() {
        match &result.result {
            Some(add_memories_response::add_memory_result::Result::Id(id)) => {
                assert!(!id.is_empty());
            }
            other => panic!("Expected Id for memory {}, got {:?}", i, other),
        }
    }
}

/// Test that memories added via add_memories are retrievable by ID.
#[tokio::test(flavor = "multi_thread")]
async fn test_add_memories_retrievable() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_add_memories_retrievable_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let memories = vec![
        make_test_memory("retrieve_1", "tag_r"),
        make_test_memory("retrieve_2", "tag_r"),
        make_test_memory("retrieve_3", "tag_r"),
    ];

    let response = client.add_memories(memories).await.unwrap();
    assert_eq!(response.results.len(), 3);

    let mut added_ids = Vec::new();
    for result in &response.results {
        if let Some(add_memories_response::add_memory_result::Result::Id(id)) = &result.result {
            added_ids.push(id.clone());
        }
    }

    // Verify each memory is retrievable.
    for id in added_ids {
        let get_response = client.get_memory_by_id(&id, None).await.unwrap();
        assert!(get_response.success, "Failed to retrieve memory {}", id);
        assert_eq!(get_response.memory.unwrap().id, id);
    }
}

/// Test that an empty batch returns an empty response.
#[tokio::test(flavor = "multi_thread")]
async fn test_add_memories_empty() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_add_memories_empty_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let response = client.add_memories(vec![]).await.unwrap();
    assert_eq!(response.results.len(), 0);
}

/// Test mixed valid/invalid: duplicate named memories should return per-item
/// errors while other memories succeed.
#[tokio::test(flavor = "multi_thread")]
async fn test_add_memories_mixed_valid_invalid() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_add_memories_mixed_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    // First add a named memory.
    let first_memory = make_named_test_memory("existing_1", "unique_name", "tag_m");
    client.add_memory(first_memory).await.unwrap();

    // Now batch: one valid, one conflicting name (different ID), one valid.
    let memories = vec![
        make_test_memory("batch_ok_1", "tag_m"),
        make_named_test_memory("batch_conflict", "unique_name", "tag_m"),
        make_test_memory("batch_ok_2", "tag_m"),
    ];

    let response = client.add_memories(memories).await.unwrap();
    assert_eq!(response.results.len(), 3);

    // First should succeed.
    let id1 = match &response.results[0].result {
        Some(add_memories_response::add_memory_result::Result::Id(id)) => id.clone(),
        _ => panic!("Expected first memory to succeed"),
    };

    // Second should fail (name conflict).
    assert!(
        matches!(
            &response.results[1].result,
            Some(add_memories_response::add_memory_result::Result::Error(_))
        ),
        "Expected second memory (name conflict) to fail"
    );

    // Third should succeed.
    let id3 = match &response.results[2].result {
        Some(add_memories_response::add_memory_result::Result::Id(id)) => id.clone(),
        _ => panic!("Expected third memory to succeed"),
    };

    // Verify the successful ones are retrievable.
    let get_response = client.get_memory_by_id(&id1, None).await.unwrap();
    assert!(get_response.success);
    let get_response = client.get_memory_by_id(&id3, None).await.unwrap();
    assert!(get_response.success);
}

/// Test that add_memories with duplicate IDs within the same batch works
/// (last write wins for Icing, both get blob IDs).
#[tokio::test(flavor = "multi_thread")]
async fn test_add_memories_with_views() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_add_memories_views_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let llm_views = LlmViews {
        llm_views: vec![LlmView {
            embedding: Some(Embedding {
                model_signature: "test_model".to_string(),
                values: vec![1.0, 0.0, 0.0],
            }),
            ..Default::default()
        }],
    };

    let memories = vec![
        Memory {
            id: "".to_string(),
            tags: vec!["tag_v".to_string()],
            views: Some(llm_views.clone()),
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        },
        Memory {
            id: "".to_string(),
            tags: vec!["tag_v".to_string()],
            views: Some(llm_views),
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        },
    ];

    let response = client.add_memories(memories).await.unwrap();
    assert_eq!(response.results.len(), 2);

    let mut added_ids = Vec::new();
    for result in &response.results {
        if let Some(add_memories_response::add_memory_result::Result::Id(id)) = &result.result {
            added_ids.push(id.clone());
        } else {
            panic!("Expected success for memory with views");
        }
    }

    // Verify retrievable.
    for id in added_ids {
        let get_response = client.get_memory_by_id(&id, None).await.unwrap();
        assert!(get_response.success, "Failed to retrieve {}", id);
    }
}

/// Looks up a memory by name, returning the response so tests can assert on
/// both the found/not-found flag and the resolved ID.
async fn get_memory_by_name(
    client: &mut PrivateMemoryClient,
    name: &str,
) -> GetMemoryByNameResponse {
    let request = GetMemoryByNameRequest { name: name.to_string(), result_mask: None };
    let response = client
        .invoke(sealed_memory_request::Request::GetMemoryByNameRequest(request))
        .await
        .unwrap();
    match response {
        sealed_memory_response::Response::GetMemoryByNameResponse(resp) => resp,
        other => panic!("unexpected response type: {other:?}"),
    }
}

/// Names must be unique, and a single `AddMemories` request must not be able to
/// smuggle two same-named memories past that rule: the per-memory check can
/// only see what is already committed, and nothing in the batch is written
/// until every memory has been validated.
#[tokio::test(flavor = "multi_thread")]
async fn test_add_memories_rejects_duplicate_name_within_batch() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_add_memories_dup_name_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    // Nothing in the database claims "shared_name" yet, so without an
    // intra-batch check both of these would be accepted.
    let memories = vec![
        make_named_test_memory("dup_first", "shared_name", "tag_d"),
        make_named_test_memory("dup_second", "shared_name", "tag_d"),
        make_test_memory("dup_unnamed", "tag_d"),
    ];

    let response = client.add_memories(memories).await.unwrap();
    assert_eq!(response.results.len(), 3);

    // The first claim on the name wins.
    let Some(add_memories_response::add_memory_result::Result::Id(dup_first_id)) =
        &response.results[0].result
    else {
        panic!("Expected the first memory to claim the name, got {:?}", response.results[0].result);
    };
    assert!(
        matches!(
            &response.results[1].result,
            Some(add_memories_response::add_memory_result::Result::Error(_))
        ),
        "Expected the second memory to be rejected as a duplicate name, got {:?}",
        response.results[1].result
    );
    // A rejected entry must not abort the rest of the batch.
    assert!(
        matches!(
            &response.results[2].result,
            Some(add_memories_response::add_memory_result::Result::Id(_))
        ),
        "Expected the unnamed memory to succeed, got {:?}",
        response.results[2].result
    );

    // The name must still resolve to exactly one memory. If both had been
    // written, this lookup would fail outright: two documents share the name
    // and the uniqueness invariant is no longer satisfiable.
    let by_name = get_memory_by_name(&mut client, "shared_name").await;
    assert!(by_name.success, "Expected the name to still resolve");
    assert_eq!(&by_name.memory.unwrap().id, dup_first_id);
}

/// The same collision, but with server-assigned IDs. Both memories have an
/// empty ID at validation time, so the check cannot treat "equal IDs" as
/// evidence that they are the same document: distinct random IDs are assigned
/// later, producing two separate documents sharing one name.
#[tokio::test(flavor = "multi_thread")]
async fn test_add_memories_rejects_duplicate_name_within_batch_without_ids() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_add_memories_dup_name_no_id_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let memories = vec![
        make_named_test_memory("", "unassigned_name", "tag_n"),
        make_named_test_memory("", "unassigned_name", "tag_n"),
    ];

    let response = client.add_memories(memories).await.unwrap();
    assert_eq!(response.results.len(), 2);

    assert!(
        matches!(
            &response.results[0].result,
            Some(add_memories_response::add_memory_result::Result::Id(_))
        ),
        "Expected the first memory to claim the name, got {:?}",
        response.results[0].result
    );
    assert!(
        matches!(
            &response.results[1].result,
            Some(add_memories_response::add_memory_result::Result::Error(_))
        ),
        "Expected the second memory to be rejected as a duplicate name, got {:?}",
        response.results[1].result
    );

    let by_name = get_memory_by_name(&mut client, "unassigned_name").await;
    assert!(by_name.success, "Expected the name to still resolve");
}
