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
    let memory_id = "test_memory_id";
    let memory_to_add = Memory {
        id: memory_id.to_string(),
        tags: vec!["test_tag".to_string()],
        views: Some(llm_view),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
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
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
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
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
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

    // Add memory that will expire in 2 seconds
    let expired_memory_to_add = Memory {
        id: expired_memory_id.to_string(),
        tags: vec!["expired".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(2),
        )),
        ..Default::default()
    };

    // Add memory that will expire in 60 seconds
    let non_expired_memory_to_add = Memory {
        id: non_expired_memory_id.to_string(),
        tags: vec!["non_expired".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(60),
        )),
        ..Default::default()
    };

    client.add_memory(expired_memory_to_add).await.unwrap();
    client.add_memory(non_expired_memory_to_add).await.unwrap();

    // Sleep 3 seconds in real time to let `expired_memory` actually expire
    tokio::time::sleep(Duration::from_secs(3)).await;

    // Try to retrieve the expired memory: should not be found
    let get_response_expired = client.get_memory_by_id(expired_memory_id, None).await.unwrap();
    assert!(!get_response_expired.success);
    assert!(get_response_expired.memory.is_none());

    // Try to retrieve the non-expired memory: should be found
    let get_response_non_expired =
        client.get_memory_by_id(non_expired_memory_id, None).await.unwrap();
    assert!(get_response_non_expired.success);
    assert_eq!(get_response_non_expired.memory.unwrap().id, non_expired_memory_id);

    // Add a memory with no expiration - should fail and close the stream
    let no_expiration_memory_to_add = Memory {
        id: no_expiration_memory_id.to_string(),
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
    let expired_memory_id = "expired_memory_id";
    let non_expired_memory_id = "non_expired_memory_id";
    let no_expiration_memory_id = "no_expiration_memory_id";

    // Add memory that will expire in 2 seconds
    let expired_memory_to_add = Memory {
        id: expired_memory_id.to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(2),
        )),
        ..Default::default()
    };

    // Add memory that will expire in 60 seconds
    let non_expired_memory_to_add = Memory {
        id: non_expired_memory_id.to_string(),
        tags: vec![tag.to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(60),
        )),
        ..Default::default()
    };

    client.add_memory(expired_memory_to_add).await.unwrap();
    client.add_memory(non_expired_memory_to_add).await.unwrap();

    // Sleep 3 seconds in real time to let `expired_memory` actually expire
    tokio::time::sleep(Duration::from_secs(3)).await;

    // Retrieve memories by tag
    let response = client.get_memories(tag, 10, None, "").await.unwrap();

    // Check that only non-expired memories are returned
    assert_eq!(response.memories.len(), 1);
    let returned_ids: HashSet<String> = response.memories.into_iter().map(|m| m.id).collect();
    assert!(returned_ids.contains(non_expired_memory_id));
    assert!(!returned_ids.contains(expired_memory_id));

    // Retrieve memories with the empty tag
    let response = client.get_memories("", 10, None, "").await.unwrap();

    // Check that only non-expired memories are returned
    assert_eq!(response.memories.len(), 1);
    let returned_ids: HashSet<String> = response.memories.into_iter().map(|m| m.id).collect();
    assert!(returned_ids.contains(non_expired_memory_id));
    assert!(!returned_ids.contains(expired_memory_id));

    // Add a memory with no expiration - should fail and close the stream
    let no_expiration_memory_to_add = Memory {
        id: no_expiration_memory_id.to_string(),
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
        id: "memory1".to_string(),
        tags: vec!["tag1".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    let memory2 = Memory {
        id: "memory2".to_string(),
        tags: vec!["tag2".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    let memory3 = Memory {
        id: "memory3".to_string(),
        tags: vec!["tag3".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

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

/// Verifies that `default_error_propagation_in_response = true` in
/// `ApplicationConfig` causes errors to be returned inside the response
/// proto even when the client does NOT set the `x-error-propagation` header.
#[tokio::test(flavor = "multi_thread")]
async fn test_default_error_propagation_in_response_config() {
    fn config_with_error_in_response(
        db_addr: std::net::SocketAddr,
    ) -> private_memory_server_lib::app::ApplicationConfig {
        let mut config = private_memory_test_utils::default_test_application_config(db_addr);
        config.default_error_propagation_in_response = true;
        config
    }

    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server_with_config(config_with_error_in_response, None).await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_config_error_user";

    // Create a client WITHOUT the x-error-propagation header
    // (propagate_errors_in_proto = false).
    let mut client = PrivateMemoryClient::create_with_start_session_config(
        &url,
        pm_uid,
        TEST_EK,
        dummy_client_session_config(),
        false, // No x-error-propagation header
    )
    .await
    .unwrap();

    // Send an invalid request to trigger an error.
    let request = UserRegistrationRequest {
        pm_uid: pm_uid.to_string(),
        key_encryption_key: vec![], // Invalid!
        ..Default::default()
    };

    // Because the server config has default_error_propagation_in_response = true,
    // the error should come back inside the response proto (not as a gRPC status
    // error).
    let response = client
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

/// Verifies that the `x-error-propagation` header can still override the
/// config. Even with `default_error_propagation_in_response = false`,
/// sending the header should propagate errors in the response proto.
#[tokio::test(flavor = "multi_thread")]
async fn test_error_propagation_header_overrides_config() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_override_error_user";

    // Server has default_error_propagation_in_response = false,
    // but the client sets the x-error-propagation header.
    let mut client = PrivateMemoryClient::create_with_start_session_config(
        &url,
        pm_uid,
        TEST_EK,
        dummy_client_session_config(),
        true, // Sets x-error-propagation: response-proto
    )
    .await
    .unwrap();

    let request = UserRegistrationRequest {
        pm_uid: pm_uid.to_string(),
        key_encryption_key: vec![],
        ..Default::default()
    };

    let response = client
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

// ── Memory source allowlist tests ──────────────────────────────────────────

fn config_with_memory_source_allowlist(
    db_addr: std::net::SocketAddr,
) -> private_memory_server_lib::app::ApplicationConfig {
    let mut config = private_memory_test_utils::default_test_application_config(db_addr);
    config.allowed_memory_sources = vec!["source_a".to_string(), "source_b".to_string()];
    config
}

fn create_memory_with_source(id: &str, source_id: &str) -> Memory {
    Memory {
        id: id.to_string(),
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
        id: "mem_no_source".to_string(),
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
        id: "mem_no_src".to_string(),
        source: None,
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    client.add_memory(memory_without).await.expect("no source accepted without allowlist");
}
