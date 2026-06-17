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

#![cfg(test)]

use std::{
    collections::HashMap,
    sync::Arc,
    time::{Duration, SystemTime},
};

use client::{PrivateMemoryAppClient, PrivateMemoryClient};
use private_memory_test_utils::{MockClock, TestContext, system_time_to_timestamp};
use sealed_memory_rust_proto::{
    oak::private_memory::{Embedding, LlmView, LlmViews, SessionConfig, memory_value},
    prelude::v1::*,
};
use tokio::time::sleep;

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

#[tokio::test(flavor = "multi_thread")]
async fn test_add_get_reset_memory_all_modes() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_add_get_reset_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let mut contents_map = HashMap::new();
    contents_map.insert(
        "text_data".to_string(),
        MemoryValue {
            value: Some(memory_value::Value::BytesVal("this is a test".as_bytes().to_vec())),
            ..Default::default()
        },
    );
    contents_map.insert(
        "string_data".to_string(),
        MemoryValue {
            value: Some(memory_value::Value::StringVal("this is a test string".to_string())),
            ..Default::default()
        },
    );
    contents_map.insert(
        "int64_data".to_string(),
        MemoryValue { value: Some(memory_value::Value::Int64Val(123456789)), ..Default::default() },
    );
    let memory_to_add = Memory {
        id: "".to_string(),
        content: Some(MemoryContent { contents: contents_map }),
        tags: vec!["tag".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let add_memory_response = client.add_memory(memory_to_add.clone()).await.unwrap();
    let memory_id_from_add = add_memory_response.id;
    client.add_memory(memory_to_add).await.unwrap();

    // GetMemoriesRequest
    let get_memories_response_1 = client.get_memories("tag", 1, None, "").await.unwrap();
    assert_eq!(get_memories_response_1.memories.len(), 1);

    let memory_content = get_memories_response_1.memories[0].content.clone().unwrap();
    assert_eq!(memory_content.contents.len(), 3);
    assert_eq!(
        memory_content.contents["text_data"].value,
        Some(memory_value::Value::BytesVal("this is a test".as_bytes().to_vec()))
    );
    assert_eq!(
        memory_content.contents["string_data"].value,
        Some(memory_value::Value::StringVal("this is a test string".to_string()))
    );
    assert_eq!(
        memory_content.contents["int64_data"].value,
        Some(memory_value::Value::Int64Val(123456789))
    );

    // GetMemoryByIdRequest
    let get_memory_by_id_response =
        client.get_memory_by_id(&memory_id_from_add, None).await.unwrap();
    assert!(get_memory_by_id_response.success);
    assert_eq!(memory_id_from_add, get_memory_by_id_response.memory.unwrap().id);

    // ResetMemoryRequest
    let reset_memory_response = client.reset_memory().await.unwrap();
    assert!(reset_memory_response.success);

    // GetMemoriesRequest again
    let get_memories_response_2 = client.get_memories("tag", 10, None, "").await.unwrap();
    assert_eq!(get_memories_response_2.memories.len(), 0);

    // Wait for the database to be deleted.
    sleep(Duration::from_secs(1)).await;
    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_concurrent_write_sessions() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_concurrent_write_sessions_user";

    // Part 1, concurrent add
    {
        let mut client1 = PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK)
            .await
            .expect("failed to create client 1");
        let mut client2 = PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK)
            .await
            .expect("failed to create client 2");

        let memory1 = create_test_memory("memory1");
        let memory2 = create_test_memory("memory2");
        let memory3 = create_test_memory("memory3");

        client1.add_memory(memory1).await.expect("failed to add memory 1");
        client2.add_memory(memory2).await.expect("failed to add memory 2");
        client2.add_memory(memory3).await.expect("failed to add memory 3");
    }

    // Part two, read back
    // We currently don't have a good signal that the peristence worker is done.
    tokio::time::sleep(Duration::from_secs(10)).await;

    {
        let mut client = PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK)
            .await
            .expect("failed to create readback client");

        expect_memory_by_id(&mut client, "memory1").await;
        expect_memory_by_id(&mut client, "memory2").await;
        expect_memory_by_id(&mut client, "memory3").await;
    }
    ctx.teardown().await;
}

async fn expect_memory_by_id(client: &mut PrivateMemoryClient, id: &str) {
    client
        .get_memory_by_id(id, None)
        .await
        .unwrap_or_else(|e| panic!("failed reading {id}: {e:?}"))
        .memory
        .unwrap_or_else(|| panic!("{id} was not present"));
}

fn create_test_memory(id: &str) -> Memory {
    let mut contents_map = HashMap::new();
    contents_map.insert(
        "string_data".to_string(),
        MemoryValue {
            value: Some(memory_value::Value::StringVal("this is a test string".to_string())),
            ..Default::default()
        },
    );
    Memory {
        id: id.to_string(),
        content: Some(MemoryContent { contents: contents_map }),
        tags: vec!["tag".to_string()],
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_memory_expiration() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_memory_expiration_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Add memory that will expire in 2 seconds
    let memory_expired = Memory {
        id: "memory_expired".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(2),
        )),
        ..Default::default()
    };
    // Add memory that will expire in 60 seconds (effectively valid during the test)
    let memory_valid = Memory {
        id: "memory_valid".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(60),
        )),
        ..Default::default()
    };
    let memory_no_expiration =
        Memory { id: "memory_no_expiration".to_string(), ..Default::default() };

    client.add_memory(memory_expired.clone()).await.unwrap();
    client.add_memory(memory_valid.clone()).await.unwrap();
    // Adding a memory without expiration should fail.
    let add_no_exp_result = client.add_memory(memory_no_expiration.clone()).await;
    assert!(add_no_exp_result.is_err());

    // Close session and wait for changes to propagate.
    drop(client);

    // Sleep 3 seconds in real time to let `memory_expired` actually expire
    sleep(Duration::from_secs(3)).await;

    // Creating a new client will trigger a key sync which will run expired memories
    // deletion.
    let mut client2 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    assert!(!client2.get_memory_by_id("memory_expired", None).await.unwrap().success);
    assert!(client2.get_memory_by_id("memory_valid", None).await.unwrap().success);

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_add_memory_expired_throws_error() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_expired_error_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Expiration in the past (10 seconds ago)
    let memory_expired = Memory {
        id: "expired_err".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            std::time::SystemTime::now() - Duration::from_secs(10),
        )),
        ..Default::default()
    };

    let result = client.add_memory(memory_expired).await;
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(format!("{:?}", err).contains("expiration_timestamp must be in the future"));

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_add_memory_too_long_ttl_throws_error() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_too_long_ttl_error_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Expiration more than 2 years in the future (2 years + 1 day)
    let too_long_ttl = Memory {
        id: "too_long_ttl".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            std::time::SystemTime::now() + Duration::from_secs(2 * 365 * 86400 + 86400),
        )),
        ..Default::default()
    };

    let result = client.add_memory(too_long_ttl).await;
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        format!("{:?}", err)
            .contains("expiration_timestamp cannot be more than 2 years in the future")
    );

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_add_memory_sets_correct_created_timestamp_with_mock_clock() {
    let mock_time = SystemTime::now();
    let mock_clock = Arc::new(MockClock::new(mock_time));

    let ctx = TestContext::setup_with_clock(mock_clock.clone()).await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_add_memory_sets_correct_created_timestamp_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let memory = Memory {
        id: "memory_without_timestamp".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(mock_time + Duration::from_secs(3600))),
        ..Default::default()
    };
    let add_memory_response = client.add_memory(memory).await.unwrap();
    let memory_id = add_memory_response.id;

    let get_memory_response = client.get_memory_by_id(&memory_id, None).await.unwrap();
    assert!(get_memory_response.success);
    let retrieved_memory = get_memory_response.memory.unwrap();

    if ctx.is_host() {
        assert_eq!(retrieved_memory.created_timestamp, Some(system_time_to_timestamp(mock_time)));
    } else {
        assert!(retrieved_memory.created_timestamp.is_some());
    }

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_add_memory_overwrites_user_created_timestamp() {
    let mock_time = SystemTime::now();
    let mock_clock = Arc::new(MockClock::new(mock_time));

    let ctx = TestContext::setup_with_clock(mock_clock.clone()).await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_add_memory_overwrites_user_created_timestamp_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let user_timestamp = prost_types::Timestamp { seconds: 123456789, nanos: 0 };
    let memory = Memory {
        id: "memory_with_timestamp".to_string(),
        created_timestamp: Some(user_timestamp),
        expiration_timestamp: Some(system_time_to_timestamp(mock_time + Duration::from_secs(3600))),
        ..Default::default()
    };
    let add_memory_response = client.add_memory(memory).await.unwrap();
    let memory_id = add_memory_response.id;

    let get_memory_response = client.get_memory_by_id(&memory_id, None).await.unwrap();
    assert!(get_memory_response.success);
    let retrieved_memory = get_memory_response.memory.unwrap();

    if ctx.is_host() {
        assert_eq!(retrieved_memory.created_timestamp, Some(system_time_to_timestamp(mock_time)));
        assert_ne!(retrieved_memory.created_timestamp, Some(user_timestamp));
    } else {
        assert!(retrieved_memory.created_timestamp.is_some());
    }

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_add_memory_duplicate_name_throws_error() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_duplicate_name_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let memory1 = Memory {
        id: "id1".to_string(),
        name: "shared_name".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let memory2 = Memory {
        id: "id2".to_string(),
        name: "shared_name".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    // Adding first memory should succeed
    let response1 = client.add_memory(memory1.clone()).await;
    assert!(response1.is_ok());

    // Adding second memory with same name but different id should fail
    let response2 = client.add_memory(memory2.clone()).await;
    assert!(response2.is_err());

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_add_memory_duplicate_name_no_id_throws_error() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_duplicate_name_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let memory1 = Memory {
        id: "id1".to_string(),
        name: "shared_name".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    let memory2 = Memory {
        name: "shared_name".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    // Adding first memory should succeed
    let response1 = client.add_memory(memory1.clone()).await;
    assert!(response1.is_ok());

    // Adding second memory with same name and no id should fail
    let response2 = client.add_memory(memory2.clone()).await;
    assert!(response2.is_err());

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_add_memory_duplicate_name_same_id_okay() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_duplicate_name_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let memory1 = Memory {
        id: "id1".to_string(),
        name: "shared_name".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };

    // Adding first memory should succeed
    let response1 = client.add_memory(memory1.clone()).await;
    assert!(response1.is_ok());

    // Adding second memory with same name and same id should succeed
    let response2 = client.add_memory(memory1.clone()).await;
    assert!(response2.is_ok());

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_get_database_metrics() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_metrics_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // ── Empty database ──────────────────────────────────────────────────
    let metrics = client.get_database_metrics().await.unwrap();
    let memory_info = metrics.memory_info.unwrap();
    assert_eq!(memory_info.memory_count, 0);
    assert_eq!(memory_info.llm_view_count, 0);

    // Even an empty DB has an underlying Icing structure, so storage should be
    // reported and non-negative.
    let storage_info = metrics.storage_info.unwrap();
    let empty_storage = storage_info.total_storage_bytes;
    assert!(empty_storage >= 0, "empty DB storage should be non-negative");

    // ── Add a memory without views ──────────────────────────────────────
    client
        .add_memory(Memory {
            tags: vec!["tag1".to_string()],
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        })
        .await
        .unwrap();

    let metrics = client.get_database_metrics().await.unwrap();
    let memory_info = metrics.memory_info.unwrap();
    assert_eq!(memory_info.memory_count, 1);
    assert_eq!(memory_info.llm_view_count, 0);

    let storage_after_one_memory = metrics.storage_info.unwrap().total_storage_bytes;
    assert!(
        storage_after_one_memory > empty_storage,
        "storage should grow after adding a memory: {} vs {}",
        storage_after_one_memory,
        empty_storage
    );

    // ── Add a memory with 2 LLM views ──────────────────────────────────
    let add_resp = client
        .add_memory(Memory {
            tags: vec!["tag2".to_string()],
            views: Some(LlmViews {
                llm_views: vec![
                    LlmView {
                        id: "view1".to_string(),
                        embedding: Some(Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![1.0, 0.0, 0.0],
                        }),
                        ..Default::default()
                    },
                    LlmView {
                        id: "view2".to_string(),
                        embedding: Some(Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![0.0, 1.0, 0.0],
                        }),
                        ..Default::default()
                    },
                ],
            }),
            expiration_timestamp: Some(system_time_to_timestamp(
                SystemTime::now() + Duration::from_secs(3600),
            )),
            ..Default::default()
        })
        .await
        .unwrap();

    let metrics = client.get_database_metrics().await.unwrap();
    let memory_info = metrics.memory_info.unwrap();
    assert_eq!(memory_info.memory_count, 2);
    assert_eq!(memory_info.llm_view_count, 2);

    let storage_after_two_memories = metrics.storage_info.unwrap().total_storage_bytes;
    assert!(
        storage_after_two_memories > storage_after_one_memory,
        "storage should grow after adding another memory with views: {} vs {}",
        storage_after_two_memories,
        storage_after_one_memory
    );

    // ── Delete the second memory ────────────────────────────────────────
    client.delete_memory(vec![add_resp.id]).await.unwrap();

    let metrics = client.get_database_metrics().await.unwrap();
    let memory_info = metrics.memory_info.unwrap();
    assert_eq!(memory_info.memory_count, 1);
    assert_eq!(memory_info.llm_view_count, 0);

    // Storage should still be reported as positive after deletion.
    let storage_after_delete = metrics.storage_info.unwrap().total_storage_bytes;
    assert!(storage_after_delete > 0, "storage should still be positive after deletion");

    // ── Reset all memory ────────────────────────────────────────────────
    client.reset_memory().await.unwrap();

    let metrics = client.get_database_metrics().await.unwrap();
    let memory_info = metrics.memory_info.unwrap();
    assert_eq!(memory_info.memory_count, 0);
    assert_eq!(memory_info.llm_view_count, 0);

    // After reset, storage should still be reported and positive (Icing
    // schema + empty structures still occupy space).
    let storage_after_reset = metrics.storage_info.unwrap().total_storage_bytes;
    assert!(storage_after_reset > 0, "storage should be positive even after reset");

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_delete_memory_concurrent_delete_succeeds_with_not_found() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_concurrent_delete_user";

    let mut client1 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let memory = Memory {
        id: "memory_to_delete".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            SystemTime::now() + Duration::from_secs(3600),
        )),
        ..Default::default()
    };
    client1.add_memory(memory).await.unwrap();

    let mut client2 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Spawn two concurrent tasks to delete the same memory.
    let handle1 =
        tokio::spawn(
            async move { client1.delete_memory(vec!["memory_to_delete".to_string()]).await },
        );

    let handle2 =
        tokio::spawn(
            async move { client2.delete_memory(vec!["memory_to_delete".to_string()]).await },
        );

    let (res1, res2) = tokio::join!(handle1, handle2);
    let res1 = res1.unwrap();
    let res2 = res2.unwrap();

    // Both should succeed. One will report the memory as not found.
    assert!(res1.is_ok(), "First delete should succeed");
    assert!(res2.is_ok(), "Second delete should succeed");

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_error_propagation_behavior() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_error_user";

    // 1. Test default behavior (propagates as gRPC status)
    let mut client_default = PrivateMemoryClient::create_with_start_session_config(
        url,
        pm_uid,
        TEST_EK,
        PrivateMemoryClient::default_session_config(),
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
        url,
        pm_uid,
        TEST_EK,
        PrivateMemoryClient::default_session_config(),
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

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_sync_database() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_sync_database_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Add a memory and then sync to force persistence.
    let memory = create_test_memory("sync_test_memory");
    client.add_memory(memory).await.unwrap();

    client.sync_database().await.unwrap();

    // A second sync should also succeed (idempotent).
    client.sync_database().await.unwrap();

    // Drop and re-create the client to prove persistence actually happened.
    drop(client);
    let mut client2 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    expect_memory_by_id(&mut client2, "sync_test_memory").await;

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_sync_database_cross_session() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_sync_database_cross_session_user";

    // Session A: add a memory and sync to persist it.
    let mut client_a =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    let memory = create_test_memory("cross_session_mem");
    client_a.add_memory(memory).await.unwrap();

    client_a.sync_database().await.unwrap();

    // Session B: a new session for the same user with NO local changes.
    // SyncDatabase should pull Session A's persisted data via rebase.
    let mut client_b =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    client_b.sync_database().await.unwrap();

    // Session B should now see the memory that Session A persisted.
    expect_memory_by_id(&mut client_b, "cross_session_mem").await;

    ctx.teardown().await;
}

/// Session 1 opens first, then Session 2 writes + syncs.
/// Session 1 reads WITHOUT syncing — should NOT see Session 2's data.
#[tokio::test(flavor = "multi_thread")]
async fn test_sync_database_stale_without_sync() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_sync_stale_user";

    // Session 1: open first (empty DB).
    let mut client1 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Session 2: write a memory and sync.
    let mut client2 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    let memory = create_test_memory("stale_mem");
    client2.add_memory(memory).await.unwrap();
    client2.sync_database().await.unwrap();

    // Session 1: read WITHOUT syncing — should NOT see the memory.
    let response = client1.get_memory_by_id("stale_mem", None).await.unwrap();
    assert!(!response.success, "Session 1 should NOT see Session 2's data without syncing");

    ctx.teardown().await;
}

/// Session 1 opens first, then Session 2 writes + syncs.
/// Session 1 syncs, THEN reads — should see Session 2's data.
#[tokio::test(flavor = "multi_thread")]
async fn test_sync_database_fresh_after_sync() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_sync_fresh_user";

    // Session 1: open first (empty DB).
    let mut client1 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Session 2: write a memory and sync.
    let mut client2 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    let memory = create_test_memory("fresh_mem");
    client2.add_memory(memory).await.unwrap();
    client2.sync_database().await.unwrap();

    // Session 1: sync to pull remote changes, then read.
    client1.sync_database().await.unwrap();

    // Now Session 1 should see the memory from Session 2.
    expect_memory_by_id(&mut client1, "fresh_mem").await;

    ctx.teardown().await;
}

/// Two sessions open concurrently for the same user.
/// Each adds its own memory; neither sees the other's data until it syncs.
#[tokio::test(flavor = "multi_thread")]
async fn test_sync_database_concurrent_sessions() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_sync_concurrent_user";

    // Session A and B open at the same time.
    let mut client_a =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    let mut client_b =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // A adds MemA, B adds MemB.
    client_a.add_memory(create_test_memory("mem_a")).await.unwrap();
    client_b.add_memory(create_test_memory("mem_b")).await.unwrap();

    // A cannot read MemB, B cannot read MemA.
    let resp = client_a.get_memory_by_id("mem_b", None).await.unwrap();
    assert!(!resp.success, "A should NOT see MemB before any sync");
    let resp = client_b.get_memory_by_id("mem_a", None).await.unwrap();
    assert!(!resp.success, "B should NOT see MemA before any sync");

    // A syncs — persists MemA but still cannot read MemB (B hasn't synced).
    client_a.sync_database().await.unwrap();
    let resp = client_a.get_memory_by_id("mem_b", None).await.unwrap();
    assert!(!resp.success, "A should NOT see MemB after A syncs (B hasn't synced yet)");
    // B still cannot read MemA (B hasn't synced).
    let resp = client_b.get_memory_by_id("mem_a", None).await.unwrap();
    assert!(!resp.success, "B should NOT see MemA before B syncs");

    // B syncs — persists MemB and pulls MemA from durable storage.
    client_b.sync_database().await.unwrap();
    expect_memory_by_id(&mut client_b, "mem_a").await;
    // A still cannot see MemB (A hasn't re-synced).
    let resp = client_a.get_memory_by_id("mem_b", None).await.unwrap();
    assert!(!resp.success, "A should NOT see MemB until A re-syncs");

    // A syncs again — now pulls MemB.
    client_a.sync_database().await.unwrap();
    expect_memory_by_id(&mut client_a, "mem_b").await;

    ctx.teardown().await;
}

/// When disable_persistence_on_close is set, dropping the client should NOT
/// persist the database, so a new session should not see the memory.
#[tokio::test(flavor = "multi_thread")]
async fn test_disable_persistence_on_close() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_disable_persist_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Re-keysync with disable_persistence_on_close = true.
    let key_sync_request = KeySyncRequest {
        pm_uid: pm_uid.to_string(),
        key_encryption_key: TEST_EK.to_vec(),
        session_config: Some(SessionConfig { disable_persistence_on_close: true }),
    };
    let response = client
        .invoke(sealed_memory_request::Request::KeySyncRequest(key_sync_request))
        .await
        .unwrap();
    match response {
        sealed_memory_response::Response::KeySyncResponse(resp) => {
            assert_eq!(resp.status(), key_sync_response::Status::Success);
        }
        _ => panic!("expected KeySyncResponse"),
    }

    // Add a memory during this non-persisting session.
    client.add_memory(create_test_memory("ephemeral_mem")).await.unwrap();
    expect_memory_by_id(&mut client, "ephemeral_mem").await;

    // Drop triggers the handler's Drop, which should skip persistence.
    drop(client);

    // Wait for the server-side handler to be dropped.
    sleep(Duration::from_secs(2)).await;

    // Reconnect — memory should NOT be present.
    let mut client2 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    let resp = client2.get_memory_by_id("ephemeral_mem", None).await.unwrap();
    assert!(!resp.success, "memory should not persist when disable_persistence_on_close is set");

    ctx.teardown().await;
}

/// Control test: with the default session config (persistence enabled),
/// dropping the client should persist the database.
#[tokio::test(flavor = "multi_thread")]
async fn test_default_persistence_on_close() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_default_persist_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Add a memory with default session config (persistence enabled).
    client.add_memory(create_test_memory("persistent_mem")).await.unwrap();
    expect_memory_by_id(&mut client, "persistent_mem").await;

    // Drop should trigger persistence.
    drop(client);

    // Small delay to let the persistence worker finish.
    sleep(Duration::from_secs(2)).await;

    // Reconnect — memory should be present.
    let mut client2 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    expect_memory_by_id(&mut client2, "persistent_mem").await;

    ctx.teardown().await;
}

/// Verifies that blob soft-deletes are deferred until after persistence.
///
/// Before the deferred-delete change, `delete_memory` immediately
/// soft-deleted the blob in external storage, making it unreadable by
/// other sessions even before the deleting session persisted its index.
///
/// After the change, the blob is only soft-deleted when the deleting
/// session calls `SyncDatabase` (which persists the index and then
/// flushes the pending blob deletes). Until that point, other sessions
/// that still reference the blob can read it.
#[tokio::test(flavor = "multi_thread")]
async fn test_deferred_blob_delete_visible_until_sync() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_deferred_blob_delete_user";

    // --- Step 1: Session A adds a memory and syncs to persist it. ---
    let mut session_a =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    session_a.add_memory(create_test_memory("deferred_del_mem")).await.unwrap();
    session_a.sync_database().await.unwrap();

    // --- Step 2: Session A deletes the memory (no sync yet). ---
    // The Icing index is updated locally, but the blob in external
    // storage should NOT be soft-deleted yet.
    session_a.delete_memory(vec!["deferred_del_mem".to_string()]).await.unwrap();

    // --- Step 3: Session B opens fresh — should still see the memory. ---
    // Session B's key_sync loads the last-persisted index (which still
    // contains the memory), and the blob is still present because
    // Session A has not yet synced.
    let mut session_b =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    expect_memory_by_id(&mut session_b, "deferred_del_mem").await;

    // --- Step 4: Session A syncs — persists the delete + flushes blobs. ---
    session_a.sync_database().await.unwrap();

    // --- Step 5: Session C opens fresh — should NOT see the memory. ---
    // The persisted index no longer contains the memory, and the blob
    // has been soft-deleted.
    let mut session_c =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();
    let resp = session_c.get_memory_by_id("deferred_del_mem", None).await.unwrap();
    assert!(!resp.success, "memory should be gone after Session A synced");

    ctx.teardown().await;
}
