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

use std::collections::HashSet;

use attestation_testing::{
    DUMMY_ATTESTATION_ID, DummySessionBindingVerifierProvider, RejectingVerifier,
    dummy_client_session_config,
};
use client::{PrivateMemoryAppClient, PrivateMemoryClient};
use oak_session::{attestation::AttestationType, config::SessionConfig, handshake::HandshakeType};
use private_memory_test_utils::{start_server, system_time_to_timestamp};
use sealed_memory_rust_proto::{
    oak::private_memory::{LlmView, LlmViews},
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
    let memory_id = "test_memory_id";
    let memory_to_add = Memory {
        id: memory_id.to_string(),
        tags: vec!["test_tag".to_string()],
        views: Some(llm_view),
        ..Default::default()
    };

    let response = client.add_memory(memory_to_add).await.unwrap();
    assert_eq!(response.id, memory_id);

    let response = client.get_memory_by_id(memory_id, None).await.unwrap();
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
        false,
    )
    .await
    .unwrap();

    let memory_id = "unattested_test_memory";
    let memory_to_add = Memory {
        id: memory_id.to_string(),
        tags: vec!["test_tag".to_string()],
        ..Default::default()
    };

    let response = client.add_memory(memory_to_add).await.unwrap();
    assert_eq!(response.id, memory_id);

    let response = client.get_memory_by_id(memory_id, None).await.unwrap();
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
        false,
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
    for i in 0..50 {
        let memory_id = format!("memory_{}", i);
        expected_ids.insert(memory_id.clone());
        let memory_to_add = Memory {
            id: memory_id,
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
            ..Default::default()
        };
        client.add_memory(memory_to_add).await.unwrap();
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

    let expired_memory_id = "expired_memory_id";
    let non_expired_memory_id = "non_expired_memory_id";
    let no_expiration_memory_id = "no_expiration_memory_id";

    // Create a timestamp in the past for an expired memory
    let past_time =
        std::time::SystemTime::now().checked_sub(std::time::Duration::from_secs(3600)).unwrap(); // 1 hour ago
    let expiration_timestamp_past = Some(system_time_to_timestamp(past_time));

    // Create a timestamp in the future for a non-expired memory
    let future_time =
        std::time::SystemTime::now().checked_add(std::time::Duration::from_secs(3600)).unwrap(); // in 1 hour
    let expiration_timestamp_future = Some(system_time_to_timestamp(future_time));

    // Add an expired memory
    let expired_memory_to_add = Memory {
        id: expired_memory_id.to_string(),
        tags: vec!["expired".to_string()],
        expiration_timestamp: expiration_timestamp_past,
        ..Default::default()
    };
    let response_expired = client.add_memory(expired_memory_to_add).await.unwrap();
    assert_eq!(response_expired.id, expired_memory_id);

    // Add a non-expired memory (expires in the future)
    let non_expired_memory_to_add = Memory {
        id: non_expired_memory_id.to_string(),
        tags: vec!["non_expired".to_string()],
        expiration_timestamp: expiration_timestamp_future,
        ..Default::default()
    };
    let response_non_expired = client.add_memory(non_expired_memory_to_add).await.unwrap();
    assert_eq!(response_non_expired.id, non_expired_memory_id);

    // Add a memory with no expiration
    let no_expiration_memory_to_add = Memory {
        id: no_expiration_memory_id.to_string(),
        tags: vec!["no_expiration".to_string()],
        expiration_timestamp: None,
        ..Default::default()
    };
    let response_no_expiration = client.add_memory(no_expiration_memory_to_add).await.unwrap();
    assert_eq!(response_no_expiration.id, no_expiration_memory_id);

    // Try to retrieve the expired memory: should not be found
    let get_response_expired = client.get_memory_by_id(expired_memory_id, None).await.unwrap();
    assert!(!get_response_expired.success);
    assert!(get_response_expired.memory.is_none());

    // Try to retrieve the non-expired memory: should be found
    let get_response_non_expired =
        client.get_memory_by_id(non_expired_memory_id, None).await.unwrap();
    assert!(get_response_non_expired.success);
    assert_eq!(get_response_non_expired.memory.unwrap().id, non_expired_memory_id);

    // Try to retrieve the no-expiration memory: should be found
    let get_response_no_expiration =
        client.get_memory_by_id(no_expiration_memory_id, None).await.unwrap();
    assert!(get_response_no_expiration.success);
    assert_eq!(get_response_no_expiration.memory.unwrap().id, no_expiration_memory_id);
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
    let expired_memory_id = "expired_memory_id";
    let non_expired_memory_id = "non_expired_memory_id";
    let no_expiration_memory_id = "no_expiration_memory_id";

    // Create a timestamp in the past for an expired memory
    let past_time =
        std::time::SystemTime::now().checked_sub(std::time::Duration::from_secs(3600)).unwrap(); // 1 hour ago
    let expiration_timestamp_past = Some(system_time_to_timestamp(past_time));

    // Create a timestamp in the future for a non-expired memory
    let future_time =
        std::time::SystemTime::now().checked_add(std::time::Duration::from_secs(3600)).unwrap(); // in 1 hour
    let expiration_timestamp_future = Some(system_time_to_timestamp(future_time));

    // Add an expired memory
    let expired_memory_to_add = Memory {
        id: expired_memory_id.to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: expiration_timestamp_past,
        ..Default::default()
    };
    client.add_memory(expired_memory_to_add).await.unwrap();

    // Add a non-expired memory (expires in the future)
    let non_expired_memory_to_add = Memory {
        id: non_expired_memory_id.to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: expiration_timestamp_future,
        ..Default::default()
    };
    client.add_memory(non_expired_memory_to_add).await.unwrap();

    // Add a memory with no expiration
    let no_expiration_memory_to_add = Memory {
        id: no_expiration_memory_id.to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: None,
        ..Default::default()
    };
    client.add_memory(no_expiration_memory_to_add).await.unwrap();

    // Retrieve memories by tag
    let response = client.get_memories(tag, 10, None, "").await.unwrap();

    // Check that only non-expired memories are returned
    assert_eq!(response.memories.len(), 2);
    let returned_ids: HashSet<String> = response.memories.into_iter().map(|m| m.id).collect();
    assert!(returned_ids.contains(non_expired_memory_id));
    assert!(returned_ids.contains(no_expiration_memory_id));
    assert!(!returned_ids.contains(expired_memory_id));

    // Retrieve memories with the empty tag
    let response = client.get_memories("", 10, None, "").await.unwrap();

    // Check that only non-expired memories are returned
    assert_eq!(response.memories.len(), 2);
    let returned_ids: HashSet<String> = response.memories.into_iter().map(|m| m.id).collect();
    assert!(returned_ids.contains(non_expired_memory_id));
    assert!(returned_ids.contains(no_expiration_memory_id));
    assert!(!returned_ids.contains(expired_memory_id));
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
    let memory1 =
        Memory { id: "memory1".to_string(), tags: vec!["tag1".to_string()], ..Default::default() };
    let memory2 =
        Memory { id: "memory2".to_string(), tags: vec!["tag2".to_string()], ..Default::default() };
    let memory3 =
        Memory { id: "memory3".to_string(), tags: vec!["tag3".to_string()], ..Default::default() };

    client.add_memory(memory1).await.unwrap();
    client.add_memory(memory2).await.unwrap();
    client.add_memory(memory3).await.unwrap();

    // Test fetching multiple memories by ID
    let response = client
        .get_memories_by_id(
            vec!["memory3".to_string(), "memory1".to_string(), "memory2".to_string()],
            None,
        )
        .await
        .unwrap();

    assert_eq!(response.memories.len(), 3);
    assert!(response.not_found_ids.is_empty());
    let returned_ids: HashSet<String> = response.memories.iter().map(|m| m.id.clone()).collect();
    assert!(returned_ids.contains("memory1"));
    assert!(returned_ids.contains("memory2"));
    assert!(returned_ids.contains("memory3"));

    // Test fetching a single memory by ID
    let response = client.get_memories_by_id(vec!["memory2".to_string()], None).await.unwrap();
    assert_eq!(response.memories.len(), 1);
    assert_eq!(response.memories[0].id, "memory2");
    assert!(response.not_found_ids.is_empty());

    // Test fetching with a non-existent ID - should return found ones and report
    // not found
    let response = client
        .get_memories_by_id(
            vec![
                "memory1".to_string(),
                "non_existent_id".to_string(),
                "memory3".to_string(),
                "another_missing".to_string(),
            ],
            None,
        )
        .await
        .unwrap();
    assert_eq!(response.memories.len(), 2);
    let returned_ids: HashSet<String> = response.memories.iter().map(|m| m.id.clone()).collect();
    assert!(returned_ids.contains("memory1"));
    assert!(returned_ids.contains("memory3"));
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

#[tokio::test(flavor = "multi_thread")]
async fn test_error_propagation_behavior() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_error_user";

    // 1. Test default behavior (propagates as gRPC status)
    let mut client_default = PrivateMemoryClient::create_with_start_session_config(
        &url,
        pm_uid,
        TEST_EK,
        dummy_client_session_config(),
        false,
    )
    .await
    .unwrap();

    // Send invalid request (empty key) to trigger an error
    let request = UserRegistrationRequest {
        pm_uid: pm_uid.to_string(),
        key_encryption_key: vec![], // Invalid!
        ..Default::default()
    };

    let result = client_default
        .invoke(sealed_memory_request::Request::UserRegistrationRequest(request.clone()))
        .await;

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(format!("{:?}", err).contains("key_encryption_key not set"));

    // 2. Test metadata-triggered behavior (propagates in response proto)
    let mut client_proto = PrivateMemoryClient::create_with_start_session_config(
        &url,
        pm_uid,
        TEST_EK,
        dummy_client_session_config(),
        true,
    )
    .await
    .unwrap();

    let response = client_proto
        .invoke(sealed_memory_request::Request::UserRegistrationRequest(request))
        .await
        .unwrap();

    match response {
        sealed_memory_response::Response::Error(status) => {
            assert_eq!(status.code, tonic::Code::InvalidArgument as i32);
            assert!(status.message.contains("key_encryption_key not set"));
        }
        _ => panic!("expected error response, got {:?}", response),
    }
}
