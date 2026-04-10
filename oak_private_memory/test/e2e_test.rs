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
    oak::private_memory::{Embedding, LlmView, LlmViews, MatchType, TextQuery, memory_value},
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
async fn test_standalone_text_query() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_standalone_text_query_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let memory1 = Memory {
        id: "memory1".to_string(),
        event_timestamp: Some(prost_types::Timestamp { seconds: 100, nanos: 0 }),
        ..Default::default()
    };
    client.add_memory(memory1).await.unwrap();

    let memory2 = Memory {
        id: "memory2".to_string(),
        event_timestamp: Some(prost_types::Timestamp { seconds: 200, nanos: 0 }),
        ..Default::default()
    };
    client.add_memory(memory2).await.unwrap();

    let memory3 = Memory {
        id: "memory3".to_string(),
        event_timestamp: Some(prost_types::Timestamp { seconds: 300, nanos: 0 }),
        ..Default::default()
    };
    client.add_memory(memory3).await.unwrap();

    // Test timestamp filtering
    let gte_query = TextQuery {
        field: MemoryField::EventTimestamp as i32,
        match_type: MatchType::Gte as i32,
        value: Some(
            sealed_memory_rust_proto::oak::private_memory::text_query::Value::TimestampVal(
                prost_types::Timestamp { seconds: 200, nanos: 0 },
            ),
        ),
    };
    let query = SearchMemoryQuery {
        clause: Some(
            sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::TextQuery(
                gte_query,
            ),
        ),
    };
    let response = client.search_memory(query, 10, None, "", false).await.unwrap();
    assert_eq!(response.results.len(), 2);
    let ids: Vec<String> = response.results.into_iter().map(|r| r.memory.unwrap().id).collect();
    assert!(ids.contains(&"memory2".to_string()));
    assert!(ids.contains(&"memory3".to_string()));

    // Test ID filtering
    let eq_query = TextQuery {
        field: MemoryField::Id as i32,
        match_type: MatchType::Equal as i32,
        value: Some(sealed_memory_rust_proto::oak::private_memory::text_query::Value::StringVal(
            "memory1".to_string(),
        )),
    };
    let query = SearchMemoryQuery {
        clause: Some(
            sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::TextQuery(
                eq_query,
            ),
        ),
    };
    let response = client.search_memory(query, 10, None, "", false).await.unwrap();
    assert_eq!(response.results.len(), 1);
    assert_eq!(response.results[0].memory.as_ref().unwrap().id, "memory1");
    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_memory_search_only_return_views_with_highest_scores() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_embedding_search_with_pagination_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    // Add memory 1 with two views.
    let memory1 = Memory {
        id: "memory1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![
                LlmView {
                    id: "view1a".to_string(),
                    embedding: Some(Embedding {
                        model_signature: "test_model".to_string(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                },
                LlmView {
                    id: "view1b".to_string(),
                    embedding: Some(Embedding {
                        model_signature: "test_model".to_string(),
                        values: vec![0.0, 1.0, 0.0],
                    }),
                    ..Default::default()
                },
            ],
        }),
        ..Default::default()
    };
    client.add_memory(memory1).await.unwrap();

    // Add memory 2 with two views.
    let memory2 = Memory {
        id: "memory2".to_string(),
        views: Some(LlmViews {
            llm_views: vec![
                LlmView {
                    id: "view2a".to_string(),
                    embedding: Some(Embedding {
                        model_signature: "test_model".to_string(),
                        values: vec![0.0, 0.0, 1.0],
                    }),
                    ..Default::default()
                },
                LlmView {
                    id: "view2b".to_string(),
                    embedding: Some(Embedding {
                        model_signature: "test_model".to_string(),
                        values: vec![1.0, 1.0, 0.0], // This view will have the highest score.
                    }),
                    ..Default::default()
                },
            ],
        }),
        ..Default::default()
    };
    client.add_memory(memory2).await.unwrap();

    // Query for memories with an embedding that is closer to memory2's view2b.
    let embedding_query = SearchMemoryQuery {
        clause: Some(
            sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::EmbeddingQuery(
                EmbeddingQuery {
                    embedding: vec![Embedding {
                        model_signature: "test_model".to_string(),
                        values: vec![1.0, 1.0, 0.0],
                    }],
                    ..Default::default()
                },
            ),
        ),
    };

    let response = client.search_memory(embedding_query, 1, None, "", false).await.unwrap();
    assert_eq!(response.results.len(), 1);
    let top_result = response.results.first().unwrap();
    assert_eq!(top_result.memory.as_ref().unwrap().id, "memory2");
    assert_eq!(top_result.score, 2.0);
    let views = top_result.memory.as_ref().unwrap().views.as_ref().unwrap();
    assert_eq!(views.llm_views.len(), 1);
    assert_eq!(views.llm_views[0].id, "view2b");
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

    let memory_expired = Memory {
        id: "memory_expired".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            std::time::SystemTime::now() - Duration::from_secs(30 * 60),
        )),
        ..Default::default()
    };
    let memory_valid = Memory {
        id: "memory_valid".to_string(),
        expiration_timestamp: Some(system_time_to_timestamp(
            std::time::SystemTime::now() + Duration::from_secs(30 * 60),
        )),
        ..Default::default()
    };
    let memory_no_expiration =
        Memory { id: "memory_no_expiration".to_string(), ..Default::default() };

    client.add_memory(memory_expired.clone()).await.unwrap();
    client.add_memory(memory_valid.clone()).await.unwrap();
    client.add_memory(memory_no_expiration.clone()).await.unwrap();

    // Close session and wait for changes to propagate.
    drop(client);
    sleep(Duration::from_secs(10)).await;

    // Creating a new client will trigger a key sync which will run expired memories
    // deletion.
    let mut client2 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    assert!(!client2.get_memory_by_id("memory_expired", None).await.unwrap().success);
    assert!(client2.get_memory_by_id("memory_valid", None).await.unwrap().success);
    assert!(client2.get_memory_by_id("memory_no_expiration", None).await.unwrap().success);

    ctx.teardown().await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_add_memory_sets_correct_created_timestamp_with_mock_clock() {
    let mock_time = SystemTime::UNIX_EPOCH + Duration::from_secs(987654321);
    let mock_clock = Arc::new(MockClock::new(mock_time));

    let ctx = TestContext::setup_with_clock(mock_clock.clone()).await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_add_memory_sets_correct_created_timestamp_user";

    let mut client =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let memory = Memory { id: "memory_without_timestamp".to_string(), ..Default::default() };
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
    let mock_time = SystemTime::UNIX_EPOCH + Duration::from_secs(111222333);
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

    let memory1 =
        Memory { id: "id1".to_string(), name: "shared_name".to_string(), ..Default::default() };

    let memory2 =
        Memory { id: "id2".to_string(), name: "shared_name".to_string(), ..Default::default() };

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

    let memory1 =
        Memory { id: "id1".to_string(), name: "shared_name".to_string(), ..Default::default() };

    let memory2 = Memory { name: "shared_name".to_string(), ..Default::default() };

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

    let memory1 =
        Memory { id: "id1".to_string(), name: "shared_name".to_string(), ..Default::default() };

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
        .add_memory(Memory { tags: vec!["tag1".to_string()], ..Default::default() })
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
async fn test_delete_memory_concurrent_delete_fails() {
    let ctx = TestContext::setup().await.unwrap();
    let url = &ctx.url;
    let pm_uid = "test_concurrent_delete_user";

    let mut client1 =
        PrivateMemoryClient::create_with_start_session(url, pm_uid, TEST_EK).await.unwrap();

    let memory = Memory { id: "memory_to_delete".to_string(), ..Default::default() };
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

    // One should succeed, one should fail (if external DB fails on not found).
    // We assert that exactly one fails.
    let err_count = [res1.is_err(), res2.is_err()].iter().filter(|&&x| x).count();
    assert_eq!(err_count, 1, "Exactly one delete should fail");

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
