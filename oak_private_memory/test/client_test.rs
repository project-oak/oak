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
    collections::{BTreeMap, BTreeSet, HashSet},
    sync::Arc,
    time::{Duration, SystemTime},
};

use attestation_testing::{
    DUMMY_ATTESTATION_ID, DummySessionBindingVerifierProvider, RejectingVerifier,
    dummy_client_session_config,
};
use client::{PrivateMemoryAppClient, PrivateMemoryClient};
use futures::{SinkExt, StreamExt, TryStreamExt, stream::BoxStream};
use metrics_testing::{Attrs, Snapshot, attrs};
use oak_proto_rust::oak::session::v1::{SessionRequest, SessionResponse};
use oak_session::{
    ClientSession, Session,
    attestation::AttestationType,
    channel::{SessionChannel, SessionInitializer},
    config::SessionConfig,
    handshake::HandshakeType,
};
use private_memory_server_lib::{app::ApplicationConfig, metrics::Metrics};
use private_memory_test_utils::{
    default_test_application_config, start_server, start_server_with_config,
    start_server_with_metrics, start_server_with_session_config_factory, system_time_to_timestamp,
};
use prost::Message;
use sealed_memory_grpc_proto::oak::private_memory::sealed_memory_service_client::SealedMemoryServiceClient;
use sealed_memory_rust_proto::{
    oak::private_memory::{
        LlmView, LlmViews, MemorySource, TextView, TextViewSort, TextViews, TlsSessionFrame,
        search_memories_sort::Sort as SortValue,
    },
    prelude::v1::*,
};

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

/// Number of init messages a client sends to complete the Noise handshake
/// with the default (unattested) client session config.
const HANDSHAKE_MESSAGES: u64 = 2;

type TestMetrics = metrics_testing::TestMetrics<Metrics>;

/// Returns [`Metrics`] wired to a private in-memory meter provider, so a test
/// can read back what the server recorded.
fn test_metrics() -> TestMetrics {
    TestMetrics::new(Metrics::new)
}

/// Starts a server with the default test config that records into `harness`,
/// and returns its URL along with the join handles that must be kept alive.
async fn start_server_recording_into(
    harness: &TestMetrics,
) -> (
    String,
    tokio::task::JoinHandle<anyhow::Result<()>>,
    tokio::task::JoinHandle<anyhow::Result<()>>,
    tokio::task::JoinHandle<()>,
) {
    let (addr, server, db, persistence) =
        start_server_with_metrics(default_test_application_config, None, harness.metrics.clone())
            .await
            .unwrap();
    (format!("http://{addr}"), server, db, persistence)
}

/// Asserts that no request failed.
#[track_caller]
fn assert_no_failures(snapshot: &Snapshot) {
    let failures = snapshot.counter_points("rpc_failure_count");
    assert!(failures.values().all(|&count| count == 0), "unexpected failures: {failures:?}");
}

#[tokio::test(flavor = "multi_thread")]
async fn test_client() {
    let harness = test_metrics();
    let (url, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server_recording_into(&harness).await;
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

    // Opening the stream counts as a session start. Every message on the
    // stream counts towards `total`: the handshake messages, then
    // registration, key sync, add and get.
    let snapshot = harness.collect();
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "SessionStart")]), 1);
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "Handshake")]), HANDSHAKE_MESSAGES);
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "total")]), HANDSHAKE_MESSAGES + 4);
    for request_type in
        ["UserRegistrationRequest", "KeySyncRequest", "AddMemoryRequest", "GetMemoryByIdRequest"]
    {
        assert_eq!(
            snapshot.counter("rpc_count", &[("request_type", request_type)]),
            1,
            "{request_type}"
        );
        let latency = snapshot.histogram("rpc_latency", &[("request_type", request_type)]);
        assert_eq!(latency.count, 1, "{request_type}");
    }
    // Each request's latency is recorded under `total` too.
    assert_eq!(snapshot.histogram("rpc_latency", &[("request_type", "total")]).count, 4);
    assert_no_failures(&snapshot);
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
    let harness = test_metrics();
    let (url, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server_recording_into(&harness).await;
    let pm_uid = "test_client_keysync_invalid_key_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let invalid_kek: &[u8; 32] = b"invalidkekinvalidkekinvalidkek_k";
    let status = client.key_sync(pm_uid, invalid_kek).await;
    assert_eq!(status.unwrap(), key_sync_response::Status::InvalidKey);
    assert_eq!(harness.collect().counter("decrypt_dek_failures", &[]), 1);
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

#[tokio::test(flavor = "multi_thread")]
async fn test_memory_with_text_views_requires_source() {
    let (addr, _server, _db, _persist) = start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, "text_views_source_user", TEST_EK)
            .await
            .unwrap();

    let text_views = TextViews {
        text_views: vec![TextView {
            view_type: "notes".to_string(),
            text: vec!["some text".to_string()],
            ..Default::default()
        }],
    };

    // Missing source with non-empty text_views should be rejected.
    let memory_no_source = Memory {
        id: "".to_string(),
        source: None,
        text_views: Some(text_views.clone()),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    let result = client.add_memory(memory_no_source).await;
    assert!(result.is_err(), "missing source with text_views should be rejected");
    let err = result.unwrap_err();
    assert!(
        format!("{:?}", err).contains("source is required"),
        "error should mention required source, got: {err:?}"
    );

    // Empty source_id with non-empty text_views should be rejected.
    let memory_empty_source_id = Memory {
        id: "".to_string(),
        source: Some(MemorySource { source_id: "".to_string() }),
        text_views: Some(text_views),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    let result = client.add_memory(memory_empty_source_id).await;
    assert!(result.is_err(), "empty source_id with text_views should be rejected");
    let err = result.unwrap_err();
    assert!(
        format!("{:?}", err).contains("source_id must not be empty"),
        "error should mention empty source_id, got: {err:?}"
    );

    // Empty text_views list without source should still be accepted.
    let memory_empty_text_views = Memory {
        id: "".to_string(),
        source: None,
        text_views: Some(TextViews { text_views: vec![] }),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    client
        .add_memory(memory_empty_text_views)
        .await
        .expect("empty text_views without source should succeed");
}

/// Verifies the Invoke RPC path: handshake, key sync, add multiple
/// memories, retrieve them all.
#[tokio::test(flavor = "multi_thread")]
async fn test_invoke_basic() {
    let harness = test_metrics();
    let (url, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server_recording_into(&harness).await;
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

    // The handshake messages, registration, key sync, the adds, the gets and
    // the batch get all count towards `total`.
    let snapshot = harness.collect();
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "SessionStart")]), 1);
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "Handshake")]), HANDSHAKE_MESSAGES);
    let requests = 2 + 2 * num_memories as u64 + 1;
    assert_eq!(
        snapshot.counter("rpc_count", &[("request_type", "total")]),
        HANDSHAKE_MESSAGES + requests
    );
    assert_no_failures(&snapshot);
}

/// Load test: compares wall-clock time for sequential Invoke dispatch vs
/// pipelined InvokeAsync dispatch on a single stream. With 150ms simulated DB
/// latency per blob read, pipelined dispatch should be significantly faster
/// because the server processes requests concurrently via FuturesOrdered.
#[tokio::test(flavor = "multi_thread")]
async fn test_invoke_async_pipelining_speedup() {
    use client::AsyncPrivateMemoryClient;

    let harness = test_metrics();
    let (url, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server_recording_into(&harness).await;
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

    // Each client opened one stream and sent its handshake messages, then
    // registration, key sync, the adds and the gets, all of which count
    // towards `total`.
    let snapshot = harness.collect();
    assert_eq!(snapshot.counter("rpc_count", &[("request_type", "SessionStart")]), 2);
    assert_eq!(
        snapshot.counter("rpc_count", &[("request_type", "Handshake")]),
        2 * HANDSHAKE_MESSAGES
    );
    let requests_per_client = HANDSHAKE_MESSAGES + 2 + 2 * num_requests as u64;
    assert_eq!(
        snapshot.counter("rpc_count", &[("request_type", "total")]),
        2 * requests_per_client
    );
    assert_no_failures(&snapshot);
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

#[tokio::test(flavor = "multi_thread")]
async fn test_add_memories_with_text_views() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_add_memories_text_views_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let text_views = TextViews {
        text_views: vec![TextView {
            view_type: "notes".to_string(),
            text: vec!["meeting notes regarding project oak".to_string()],
            ..Default::default()
        }],
    };

    let memories = vec![Memory {
        id: "".to_string(),
        tags: vec!["tag_tv".to_string()],
        source: Some(MemorySource { source_id: "test_src".to_string() }),
        text_views: Some(text_views),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    }];

    let response = client.add_memories(memories).await.unwrap();
    assert_eq!(response.results.len(), 1);

    let id = match &response.results[0].result {
        Some(add_memories_response::add_memory_result::Result::Id(id)) => id.clone(),
        _ => panic!("Expected success for memory with text views"),
    };

    // Verify retrievable and text_views present.
    let get_response = client.get_memory_by_id(&id, None).await.unwrap();
    assert!(get_response.success, "Failed to retrieve {}", id);
    let retrieved_mem = get_response.memory.unwrap();
    assert!(retrieved_mem.text_views.is_some());
    let tv = &retrieved_mem.text_views.unwrap().text_views[0];
    assert!(!tv.id.is_empty());
    assert_eq!(tv.view_type, "notes");
    assert_eq!(tv.text, vec!["meeting notes regarding project oak"]);
}

#[tokio::test(flavor = "multi_thread")]
async fn test_search_memories_text_view_sort_client() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_search_text_views_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK).await.unwrap();

    let mem1 = Memory {
        id: "".to_string(),
        tags: vec!["search_test".to_string()],
        source: Some(MemorySource { source_id: "app_src".to_string() }),
        text_views: Some(TextViews {
            text_views: vec![TextView {
                view_type: "article".to_string(),
                text: vec!["quantum computing advances".to_string()],
                ..Default::default()
            }],
        }),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let mem2 = Memory {
        id: "".to_string(),
        tags: vec!["search_test".to_string()],
        source: Some(MemorySource { source_id: "app_src".to_string() }),
        text_views: Some(TextViews {
            text_views: vec![TextView {
                view_type: "article".to_string(),
                text: vec!["classical computing history".to_string()],
                ..Default::default()
            }],
        }),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let response = client.add_memories(vec![mem1, mem2]).await.unwrap();
    assert_eq!(response.results.len(), 2);

    let search_req = SearchMemoriesRequest {
        sort: vec![SearchMemoriesSort {
            sort: Some(SortValue::TextViewSort(TextViewSort {
                keywords: vec!["quantum".to_string()],
                view_type: "".to_string(),
            })),
        }],
        page_size: 10,
        ..Default::default()
    };

    let search_resp = client
        .invoke(sealed_memory_request::Request::SearchMemoriesRequest(search_req))
        .await
        .unwrap();

    match search_resp {
        sealed_memory_response::Response::SearchMemoriesResponse(resp) => {
            assert_eq!(resp.results.len(), 2);

            let mem1 = resp.results[0].memory.as_ref().unwrap();
            let tv1 = &mem1.text_views.as_ref().unwrap().text_views[0];
            assert_eq!(tv1.text, vec!["quantum computing advances"]);

            let mem2 = resp.results[1].memory.as_ref().unwrap();
            let tv2 = &mem2.text_views.as_ref().unwrap().text_views[0];
            assert_eq!(tv2.text, vec!["classical computing history"]);
        }
        other => panic!("unexpected response: {other:?}"),
    }
}

/// A session RPC.
#[derive(Clone, Copy, Debug)]
enum SessionRpc {
    Invoke,
    InvokeAsync,
    StartSession,
    StartTlsSession,
}

/// The session RPCs that run a Noise session.
const NOISE_RPCS: [SessionRpc; 3] =
    [SessionRpc::Invoke, SessionRpc::InvokeAsync, SessionRpc::StartSession];

/// The responses of a Noise session stream.
type NoiseResponses = BoxStream<'static, tonic::Result<SessionResponse>>;

/// Buffer size of the request channel; tests send one message at a time.
const RAW_REQUEST_BUFFER: usize = 10;

/// Opens a stream with the Noise session RPC `rpc`, and returns its request
/// sender and responses, or the status the server rejected it with.
async fn open_noise_stream(
    url: &str,
    rpc: SessionRpc,
) -> tonic::Result<(futures::channel::mpsc::Sender<SessionRequest>, NoiseResponses)> {
    let mut client = SealedMemoryServiceClient::connect(url.to_string()).await.unwrap();
    let (requests, request_stream) = futures::channel::mpsc::channel(RAW_REQUEST_BUFFER);
    let responses = match rpc {
        SessionRpc::Invoke => client.invoke(request_stream).await?.into_inner().boxed(),
        SessionRpc::InvokeAsync => client.invoke_async(request_stream).await?.into_inner().boxed(),
        SessionRpc::StartSession => client
            .start_session(
                request_stream
                    .map(|request| SealedMemorySessionRequest { session_request: Some(request) }),
            )
            .await?
            .into_inner()
            .map_ok(|response| response.session_response.expect("missing session response"))
            .boxed(),
        SessionRpc::StartTlsSession => panic!("{rpc:?} does not run a Noise session"),
    };
    Ok((requests, responses))
}

/// Returns the error status that a response stream ended with, given its next
/// item.
fn expect_error<T: std::fmt::Debug>(next: Option<tonic::Result<T>>) -> tonic::Status {
    match next {
        Some(Err(status)) => status,
        other => panic!("expected the stream to fail, got {other:?}"),
    }
}

/// Opens a stream with the Noise session RPC `rpc` and sends a first handshake
/// message that the server cannot handle, returning the status the server
/// ends the stream with.
async fn send_invalid_handshake(url: &str, rpc: SessionRpc) -> tonic::Status {
    let (mut requests, mut responses) = open_noise_stream(url, rpc).await.unwrap();
    requests.send(SessionRequest::default()).await.unwrap();
    expect_error(responses.next().await)
}

/// The `rpc_count` series for `request_type`.
fn request_series(request_type: &str) -> Attrs {
    attrs(&[("request_type", request_type)])
}

/// The `rpc_failure_count` series for `request_type` and `status_code`.
fn failure_series(request_type: &str, status_code: &str) -> Attrs {
    attrs(&[("request_type", request_type), ("status_code", status_code)])
}

/// Asserts that, since `before`, exactly the `rpc_count` series in `requests`
/// and the `rpc_failure_count` series in `failures`, given as `(request_type,
/// status_code, increase)`, increased, by the given amounts.
#[track_caller]
fn assert_increments(
    harness: &TestMetrics,
    before: &Snapshot,
    requests: &[(&str, u64)],
    failures: &[(&str, &str, u64)],
    context: impl std::fmt::Debug,
) {
    let snapshot = harness.collect();
    let expected_requests: BTreeMap<_, _> =
        requests.iter().map(|&(name, increase)| (request_series(name), increase)).collect();
    assert_eq!(
        snapshot.counter_increments(before, "rpc_count"),
        expected_requests,
        "rpc_count for {context:?}"
    );
    let expected_failures: BTreeMap<_, _> = failures
        .iter()
        .map(|&(name, code, increase)| (failure_series(name, code), increase))
        .collect();
    assert_eq!(
        snapshot.counter_increments(before, "rpc_failure_count"),
        expected_failures,
        "rpc_failure_count for {context:?}"
    );
}

/// A first handshake message that the server cannot handle fails the
/// handshake, on every Noise session RPC.
#[tokio::test(flavor = "multi_thread")]
async fn test_invalid_handshake_is_counted() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) = start_server_recording_into(&harness).await;

    for rpc in NOISE_RPCS {
        let before = harness.collect();
        let status = send_invalid_handshake(&url, rpc).await;
        assert_eq!(status.code(), tonic::Code::Internal, "{rpc:?}");
        assert_increments(
            &harness,
            &before,
            &[("SessionStart", 1), ("Handshake", 1), ("total", 1)],
            &[("Handshake", "INTERNAL", 1), ("total", "INTERNAL", 1)],
            rpc,
        );
    }
}

/// A raw Noise session over a session RPC stream, for sending requests that
/// `PrivateMemoryClient` cannot produce.
struct RawNoiseSession {
    session: ClientSession,
    requests: futures::channel::mpsc::Sender<SessionRequest>,
    responses: NoiseResponses,
}

impl RawNoiseSession {
    /// Opens a stream with the Noise session RPC `rpc` and completes the
    /// handshake.
    async fn open(url: &str, rpc: SessionRpc) -> Self {
        let (mut requests, mut responses) = open_noise_stream(url, rpc).await.unwrap();
        let mut session =
            ClientSession::create(PrivateMemoryClient::default_session_config()).unwrap();
        while !session.is_open() {
            requests.send(session.next_init_message().unwrap()).await.unwrap();
            if !session.is_open() {
                let response = responses.next().await.unwrap().unwrap();
                session.handle_init_message(response).unwrap();
            }
        }
        Self { session, requests, responses }
    }

    /// Sends `request` and returns the error status the server ends the
    /// stream with.
    async fn send_expecting_error(mut self, request: SessionRequest) -> tonic::Status {
        self.requests.send(request).await.unwrap();
        expect_error(self.responses.next().await)
    }

    /// Sends a request that cannot be decrypted.
    async fn send_undecryptable(self) -> tonic::Status {
        self.send_expecting_error(SessionRequest::default()).await
    }

    /// Sends a correctly encrypted payload that is not a valid
    /// `SealedMemoryRequest`, so the application handler fails.
    async fn send_undecodable(mut self) -> tonic::Status {
        let request = self.session.encrypt(vec![0xFF; 4]).unwrap();
        self.send_expecting_error(request).await
    }

    /// Sends `request` and returns the response.
    async fn invoke(&mut self, request: sealed_memory_request::Request) -> SealedMemoryResponse {
        let request = SealedMemoryRequest { request: Some(request), request_id: 1 };
        self.requests.send(self.session.encrypt(request.encode_to_vec()).unwrap()).await.unwrap();
        let response = self.responses.next().await.unwrap().unwrap();
        SealedMemoryResponse::decode(self.session.decrypt(response).unwrap().as_slice()).unwrap()
    }

    /// Ends the request stream, and waits for the server to end the session,
    /// after which it records nothing more for it.
    async fn close(self) {
        let Self { requests, mut responses, .. } = self;
        drop(requests);
        while let Some(response) = responses.next().await {
            response.expect("the session should end without an error");
        }
    }
}

/// After the handshake, a request that cannot be decrypted fails as a
/// decryption failure, on every Noise session RPC.
#[tokio::test(flavor = "multi_thread")]
async fn test_undecryptable_request_is_counted() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) = start_server_recording_into(&harness).await;

    for rpc in NOISE_RPCS {
        let before = harness.collect();
        let status = RawNoiseSession::open(&url, rpc).await.send_undecryptable().await;
        assert_eq!(status.code(), tonic::Code::InvalidArgument, "{rpc:?}");
        assert_increments(
            &harness,
            &before,
            &[
                ("SessionStart", 1),
                ("Handshake", HANDSHAKE_MESSAGES),
                ("total", HANDSHAKE_MESSAGES + 1),
                ("DecryptionFailure", 1),
            ],
            &[("DecryptionFailure", "INVALID_ARGUMENT", 1), ("total", "INVALID_ARGUMENT", 1)],
            rpc,
        );
    }
}

/// A request that decrypts to something other than a `SealedMemoryRequest`
/// fails as a deserialization failure, on every Noise session RPC.
#[tokio::test(flavor = "multi_thread")]
async fn test_undecodable_request_is_counted() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) = start_server_recording_into(&harness).await;

    for rpc in NOISE_RPCS {
        let before = harness.collect();
        let status = RawNoiseSession::open(&url, rpc).await.send_undecodable().await;
        assert_eq!(status.code(), tonic::Code::Internal, "{rpc:?}");
        assert_increments(
            &harness,
            &before,
            &[
                ("SessionStart", 1),
                ("Handshake", HANDSHAKE_MESSAGES),
                ("total", HANDSHAKE_MESSAGES + 1),
                ("DeserializationFailure", 1),
            ],
            &[("DeserializationFailure", "INTERNAL", 1), ("total", "INTERNAL", 1)],
            rpc,
        );
    }
}

/// A request that the application rejects before key sync.
fn add_memory_request() -> sealed_memory_request::Request {
    sealed_memory_request::Request::AddMemoryRequest(AddMemoryRequest::default())
}

/// Returns the code of the error that `response` carries.
fn error_code(response: &SealedMemoryResponse) -> tonic::Code {
    match &response.response {
        Some(sealed_memory_response::Response::Error(status)) => tonic::Code::from(status.code),
        other => panic!("expected an error response, got {other:?}"),
    }
}

/// A request that the application rejects with an error response fails
/// under its own request type, exactly once, on every Noise session RPC.
#[tokio::test(flavor = "multi_thread")]
async fn test_rejected_request_is_counted_once() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) = start_server_recording_into(&harness).await;

    for rpc in NOISE_RPCS {
        let before = harness.collect();
        let mut session = RawNoiseSession::open(&url, rpc).await;
        let response = session.invoke(add_memory_request()).await;
        session.close().await;
        assert_eq!(error_code(&response), tonic::Code::FailedPrecondition, "{rpc:?}");
        assert_increments(
            &harness,
            &before,
            &[
                ("SessionStart", 1),
                ("Handshake", HANDSHAKE_MESSAGES),
                ("total", HANDSHAKE_MESSAGES + 1),
                ("AddMemoryRequest", 1),
            ],
            &[("AddMemoryRequest", "FAILED_PRECONDITION", 1), ("total", "FAILED_PRECONDITION", 1)],
            rpc,
        );
    }
}

/// Sends a `StartSession` message without a session request, and returns the
/// status the server ends the stream with.
async fn send_without_session_request(url: &str) -> tonic::Status {
    let mut client = SealedMemoryServiceClient::connect(url.to_string()).await.unwrap();
    let (mut requests, request_stream) = futures::channel::mpsc::channel(RAW_REQUEST_BUFFER);
    let mut responses = client.start_session(request_stream).await.unwrap().into_inner();
    requests.send(SealedMemorySessionRequest { session_request: None }).await.unwrap();
    expect_error(responses.next().await)
}

/// A `StartSession` message without a session request fails as an empty
/// request.
#[tokio::test(flavor = "multi_thread")]
async fn test_message_without_session_request_is_counted() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) = start_server_recording_into(&harness).await;
    let before = harness.collect();

    let status = send_without_session_request(&url).await;

    assert_eq!(status.code(), tonic::Code::InvalidArgument);
    assert_increments(
        &harness,
        &before,
        &[("SessionStart", 1), ("total", 1), ("EmptyRequest", 1)],
        &[("EmptyRequest", "INVALID_ARGUMENT", 1), ("total", "INVALID_ARGUMENT", 1)],
        SessionRpc::StartSession,
    );
}

/// Opens a stream with `rpc`, and returns the status the server rejected it
/// with.
async fn open_rejected_stream(url: &str, rpc: SessionRpc) -> tonic::Status {
    let result = match rpc {
        SessionRpc::StartTlsSession => {
            let mut client = SealedMemoryServiceClient::connect(url.to_string()).await.unwrap();
            let (_requests, request_stream) =
                futures::channel::mpsc::channel::<TlsSessionFrame>(RAW_REQUEST_BUFFER);
            client.start_tls_session(request_stream).await.map(drop)
        }
        _ => open_noise_stream(url, rpc).await.map(drop),
    };
    result.expect_err("the server should have rejected the stream")
}

/// A `StartTlsSession` stream is rejected if TLS is not configured, and counted
/// as a failed session start.
#[tokio::test(flavor = "multi_thread")]
async fn test_tls_session_without_tls_is_counted() {
    let harness = test_metrics();
    let (url, _server, _db, _persistence) = start_server_recording_into(&harness).await;
    let before = harness.collect();

    let status = open_rejected_stream(&url, SessionRpc::StartTlsSession).await;

    assert_eq!(status.code(), tonic::Code::Unimplemented);
    assert_increments(
        &harness,
        &before,
        &[("SessionStart", 1)],
        &[("SessionStart", "UNIMPLEMENTED", 1)],
        SessionRpc::StartTlsSession,
    );
}

/// A session config that the server cannot create a session from: it verifies
/// the peer, but has no verifier for it.
fn unusable_session_config() -> SessionConfig {
    SessionConfig::builder(AttestationType::PeerUnidirectional, HandshakeType::NoiseNN).build()
}

/// A Noise session stream is rejected if the server cannot create its
/// session, and counted as a failed session start.
#[tokio::test(flavor = "multi_thread")]
async fn test_session_creation_failure_is_counted() {
    let harness = test_metrics();
    let (addr, _server, _db, _persistence) = start_server_with_session_config_factory(
        default_test_application_config,
        None,
        Arc::new(unusable_session_config),
        harness.metrics.clone(),
    )
    .await
    .unwrap();
    let url = format!("http://{addr}");

    for rpc in NOISE_RPCS {
        let before = harness.collect();
        let status = open_rejected_stream(&url, rpc).await;
        assert_eq!(status.code(), tonic::Code::FailedPrecondition, "{rpc:?}");
        assert_increments(
            &harness,
            &before,
            &[("SessionStart", 1)],
            &[("SessionStart", "FAILED_PRECONDITION", 1)],
            rpc,
        );
    }
}

/// Every `status_code` label: the canonical names of the gRPC status codes,
/// which the host's pstreamz policy allows.
const STATUS_CODE_LABELS: [&str; 17] = [
    "OK",
    "CANCELLED",
    "UNKNOWN",
    "INVALID_ARGUMENT",
    "DEADLINE_EXCEEDED",
    "NOT_FOUND",
    "ALREADY_EXISTS",
    "PERMISSION_DENIED",
    "RESOURCE_EXHAUSTED",
    "FAILED_PRECONDITION",
    "ABORTED",
    "OUT_OF_RANGE",
    "UNIMPLEMENTED",
    "INTERNAL",
    "UNAVAILABLE",
    "DATA_LOSS",
    "UNAUTHENTICATED",
];

/// The host derives the `rpc_failure_count` columns from a single exported
/// point, and drops all later metrics if another point doesn't match them. So
/// after failures on many paths, every point must still carry exactly a
/// `request_type` registered at startup (the request types that can fail,
/// which the metrics unit tests pin down) and a `status_code` label.
#[tokio::test(flavor = "multi_thread")]
async fn test_failure_points_have_request_type_and_status_code() {
    let harness = test_metrics();
    let registered: BTreeSet<String> = harness
        .collect()
        .counter_points("rpc_failure_count")
        .keys()
        .flatten()
        .filter(|(key, _)| key == "request_type")
        .map(|(_, value)| value.clone())
        .collect();
    let (url, _server, _db, _persistence) = start_server_recording_into(&harness).await;

    for rpc in NOISE_RPCS {
        send_invalid_handshake(&url, rpc).await;
        RawNoiseSession::open(&url, rpc).await.send_undecryptable().await;
        RawNoiseSession::open(&url, rpc).await.send_undecodable().await;
        let mut session = RawNoiseSession::open(&url, rpc).await;
        session.invoke(add_memory_request()).await;
        session.close().await;
    }
    send_without_session_request(&url).await;
    open_rejected_stream(&url, SessionRpc::StartTlsSession).await;

    let snapshot = harness.collect();
    let mut recorded_codes = BTreeSet::new();
    for (series, &count) in snapshot.counter_points("rpc_failure_count") {
        let [(request_type_key, request_type), (status_code_key, status_code)] = series.as_slice()
        else {
            panic!("expected exactly two attributes: {series:?}");
        };
        assert_eq!(
            [request_type_key.as_str(), status_code_key.as_str()],
            ["request_type", "status_code"],
            "{series:?}"
        );
        assert!(registered.contains(request_type), "unregistered request type: {series:?}");
        assert!(STATUS_CODE_LABELS.contains(&status_code.as_str()), "unknown status: {series:?}");
        if count > 0 {
            recorded_codes.insert(status_code.as_str());
        }
    }
    // The paths above failed with more codes than the zero-initialized one.
    assert_eq!(
        recorded_codes,
        BTreeSet::from(["FAILED_PRECONDITION", "INTERNAL", "INVALID_ARGUMENT", "UNIMPLEMENTED"])
    );
}

/// Server config whose minimum available memory ratio no real host meets, so
/// every new session is rejected as low on memory.
fn config_with_unreachable_memory_threshold(db_addr: std::net::SocketAddr) -> ApplicationConfig {
    ApplicationConfig {
        // No real host has this much of its memory available.
        min_available_memory_ratio: 0.999_999,
        ..default_test_application_config(db_addr)
    }
}

/// Every session RPC.
const ALL_RPCS: [SessionRpc; 4] = [
    SessionRpc::Invoke,
    SessionRpc::InvokeAsync,
    SessionRpc::StartSession,
    SessionRpc::StartTlsSession,
];

/// New sessions are rejected while available memory is below the configured
/// threshold, on every session RPC, and each rejection is counted.
#[tokio::test(flavor = "multi_thread")]
async fn test_low_memory_rejections_are_counted() {
    let harness = test_metrics();
    let (addr, _server, _db, _persistence) = start_server_with_metrics(
        config_with_unreachable_memory_threshold,
        None,
        harness.metrics.clone(),
    )
    .await
    .unwrap();
    let url = format!("http://{addr}");

    for rpc in ALL_RPCS {
        let before = harness.collect();
        let status = open_rejected_stream(&url, rpc).await;
        assert_eq!(
            status.code(),
            tonic::Code::ResourceExhausted,
            "{rpc:?} was not rejected for low memory ({status:?}); the server only rejects \
             sessions for low memory if /proc/meminfo is readable"
        );
        assert_increments(
            &harness,
            &before,
            &[("SessionStart", 1)],
            &[("SessionStart", "RESOURCE_EXHAUSTED", 1)],
            rpc,
        );
        assert_eq!(
            harness.collect().counter_increments(&before, "session_rejected_low_memory"),
            BTreeMap::from([(attrs(&[]), 1)]),
            "{rpc:?}"
        );
        assert_eq!(
            harness.collect().counter_increments(&before, "session_rejected"),
            BTreeMap::from([(attrs(&[("reason", "low_memory")]), 1)]),
            "{rpc:?}"
        );
    }
}

fn config_with_single_session_cap(db_addr: std::net::SocketAddr) -> ApplicationConfig {
    ApplicationConfig { max_active_sessions: 1, ..default_test_application_config(db_addr) }
}

/// Once `max_active_sessions` live sessions are open, new sessions are
/// rejected on every session RPC and counted under `reason=max_sessions`.
#[tokio::test(flavor = "multi_thread")]
async fn test_session_cap_rejections_are_counted() {
    let harness = test_metrics();
    let (addr, _server, _db, _persistence) =
        start_server_with_metrics(config_with_single_session_cap, None, harness.metrics.clone())
            .await
            .unwrap();
    let url = format!("http://{addr}");

    let held = RawNoiseSession::open(&url, SessionRpc::Invoke).await;
    let snapshot = harness.collect();
    assert_eq!(snapshot.gauge_points("active_sessions"), &BTreeMap::from([(attrs(&[]), 1)]));
    assert_eq!(snapshot.gauge_points("max_active_sessions"), &BTreeMap::from([(attrs(&[]), 1)]));

    for rpc in ALL_RPCS {
        let before = harness.collect();
        let status = open_rejected_stream(&url, rpc).await;
        assert_eq!(status.code(), tonic::Code::ResourceExhausted, "{rpc:?}: {status:?}");
        assert_increments(
            &harness,
            &before,
            &[("SessionStart", 1)],
            &[("SessionStart", "RESOURCE_EXHAUSTED", 1)],
            rpc,
        );
        assert_eq!(
            harness.collect().counter_increments(&before, "session_rejected"),
            BTreeMap::from([(attrs(&[("reason", "max_sessions")]), 1)]),
            "{rpc:?}"
        );
    }
    held.close().await;
}

fn config_with_unreachable_map_count_ratio(db_addr: std::net::SocketAddr) -> ApplicationConfig {
    ApplicationConfig {
        // Rounds the map-count limit down to 0, which any running process exceeds.
        max_map_count_ratio: f64::MIN_POSITIVE,
        ..default_test_application_config(db_addr)
    }
}

/// New sessions are rejected while the process map count is at or above the
/// configured ratio, on every session RPC, and counted under
/// `reason=map_count`.
#[tokio::test(flavor = "multi_thread")]
async fn test_map_count_rejections_are_counted() {
    let harness = test_metrics();
    let (addr, _server, _db, _persistence) = start_server_with_metrics(
        config_with_unreachable_map_count_ratio,
        None,
        harness.metrics.clone(),
    )
    .await
    .unwrap();
    let url = format!("http://{addr}");

    for rpc in ALL_RPCS {
        let before = harness.collect();
        let status = open_rejected_stream(&url, rpc).await;
        assert_eq!(status.code(), tonic::Code::ResourceExhausted, "{rpc:?}: {status:?}");
        assert_increments(
            &harness,
            &before,
            &[("SessionStart", 1)],
            &[("SessionStart", "RESOURCE_EXHAUSTED", 1)],
            rpc,
        );
        assert_eq!(
            harness.collect().counter_increments(&before, "session_rejected"),
            BTreeMap::from([(attrs(&[("reason", "map_count")]), 1)]),
            "{rpc:?}"
        );
    }
}
