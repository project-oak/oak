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

use client::{PrivateMemoryClient, SerializationFormat};
use private_memory_test_utils::{start_server, system_time_to_timestamp};
use sealed_memory_rust_proto::{
    oak::private_memory::{LlmView, LlmViews, MatchType, TextQuery, text_query},
    prelude::v1::*,
};

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

#[tokio::test(flavor = "multi_thread")]
async fn test_client() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();
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
}

#[tokio::test(flavor = "multi_thread")]
async fn test_client_pagination() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_pagination_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

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

        // Test SearchMemory pagination
        let query = SearchMemoryQuery {
            clause: Some(
                sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::EmbeddingQuery(
                    EmbeddingQuery {
                        embedding: vec![Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![1.0, 0.0, 0.0],
                        }],
                        ..Default::default()
                    },
                ),
            ),
        };
        let mut actual_ids_search = HashSet::new();
        let mut next_page_token = "".to_string();
        for _ in 0..10 {
            let response = client
                .search_memory(query.clone(), 5, None, &next_page_token, false)
                .await
                .unwrap();
            for result in response.results {
                actual_ids_search.insert(result.memory.unwrap().id);
            }
            next_page_token = response.next_page_token;
            if next_page_token.is_empty() {
                break;
            }
        }
        assert_eq!(expected_ids, actual_ids_search);
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_client_text_query() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_text_query_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

        let memory1 = Memory {
            id: "memory1".to_string(),
            created_timestamp: Some(prost_types::Timestamp { seconds: 100, nanos: 0 }),
            ..Default::default()
        };
        client.add_memory(memory1).await.unwrap();

        let memory2 = Memory {
            id: "memory2".to_string(),
            created_timestamp: Some(prost_types::Timestamp { seconds: 200, nanos: 0 }),
            ..Default::default()
        };
        client.add_memory(memory2).await.unwrap();

        let memory3 = Memory {
            id: "memory3".to_string(),
            created_timestamp: Some(prost_types::Timestamp { seconds: 300, nanos: 0 }),
            ..Default::default()
        };
        client.add_memory(memory3).await.unwrap();

        // Test timestamp filtering
        let gte_query = TextQuery {
            field: MemoryField::CreatedTimestamp as i32,
            match_type: MatchType::Gte as i32,
            value: Some(text_query::Value::TimestampVal(prost_types::Timestamp {
                seconds: 200,
                nanos: 0,
            })),
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
            value: Some(text_query::Value::StringVal("memory1".to_string())),
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
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_client_keep_all_llm_views() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_keep_all_llm_views_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

        let llm_view1 = LlmView {
            embedding: Some(Embedding {
                model_signature: "test_model_1".to_string(),
                values: vec![1.0, 0.0, 0.0],
            }),
            ..Default::default()
        };
        let llm_view2 = LlmView {
            embedding: Some(Embedding {
                model_signature: "test_model_2".to_string(),
                values: vec![0.0, 1.0, 0.0],
            }),
            ..Default::default()
        };
        let llm_view3 = LlmView {
            embedding: Some(Embedding {
                model_signature: "test_model_3".to_string(),
                values: vec![0.0, 0.0, 1.0],
            }),
            ..Default::default()
        };

        let llm_views =
            LlmViews { llm_views: vec![llm_view1.clone(), llm_view2.clone(), llm_view3.clone()] };
        let memory_id = "test_memory_with_multiple_views";
        let memory_to_add = Memory {
            id: memory_id.to_string(),
            tags: vec!["test_tag_multiple_views".to_string()],
            views: Some(llm_views),
            ..Default::default()
        };

        client.add_memory(memory_to_add).await.unwrap();

        let query = SearchMemoryQuery {
            clause: Some(
                sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::TextQuery(
                    TextQuery {
                        field: MemoryField::Id as i32,
                        match_type: MatchType::Equal as i32,
                        value: Some(text_query::Value::StringVal(memory_id.to_string())),
                    },
                ),
            ),
        };

        let response = client.search_memory(query.clone(), 10, None, "", true).await.unwrap();
        assert_eq!(response.results.len(), 1);
        let returned_memory = response.results[0].memory.as_ref().unwrap();
        let returned_llm_views = returned_memory.views.as_ref().unwrap().llm_views.clone();
        assert_eq!(returned_llm_views.len(), 3);

        let returned_model_signatures = returned_llm_views
            .into_iter()
            .map(|v| v.embedding.unwrap().model_signature)
            .collect::<HashSet<String>>();

        let mut expected_model_signatures = HashSet::new();
        expected_model_signatures.insert("test_model_1".to_string());
        expected_model_signatures.insert("test_model_2".to_string());
        expected_model_signatures.insert("test_model_3".to_string());

        assert_eq!(returned_model_signatures, expected_model_signatures);

        // Test that when keep_all_llm_views is false, the llm views are not returned.
        let response_no_views = client.search_memory(query, 10, None, "", false).await.unwrap();
        assert_eq!(response_no_views.results.len(), 1);
        let returned_memory_no_views = response_no_views.results[0].memory.as_ref().unwrap();
        assert!(
            returned_memory_no_views.views.is_none()
                || returned_memory_no_views.views.as_ref().unwrap().llm_views.is_empty()
        );
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_client_keysync_invalid_key() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_keysync_invalid_key_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

        let invalid_kek: &[u8; 32] = b"invalidkekinvalidkekinvalidkek_k";
        let status = client.key_sync(pm_uid, invalid_kek).await;
        assert_eq!(status.unwrap(), key_sync_response::Status::InvalidKey);
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn search_with_view_scores() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();
        let memory_id = "memory_id_view_scores".to_string();
        let memory = Memory {
            id: memory_id.clone(),
            tags: vec!["tag".to_string()],
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
        };
        client.add_memory(memory).await.unwrap();

        let embedding_query = SearchMemoryQuery {
            clause: Some(
                sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::EmbeddingQuery(
                    EmbeddingQuery {
                        embedding: vec![Embedding {
                            model_signature: "test_model".to_string(),
                            values: vec![0.7, 0.9, 0.0],
                        }],
                        ..Default::default()
                    },
                ),
            ),
        };

        let response = client.search_memory(embedding_query, 10, None, "", false).await.unwrap();
        assert_eq!(response.results.len(), 1);
        let result = &response.results[0];
        assert_eq!(result.memory.as_ref().unwrap().id, memory_id);
        assert_eq!(result.view_scores, vec![0.9, 0.7]);
        // assert the views in the memory are view1 and view2
        let returned_view_ids = result
            .memory
            .as_ref()
            .unwrap()
            .views
            .as_ref()
            .unwrap()
            .llm_views
            .clone()
            .into_iter()
            .map(|v| v.id)
            .collect::<Vec<String>>();
        assert_eq!(returned_view_ids, vec!["view2".to_string(), "view1".to_string()]);
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_get_by_id_with_expired_memories() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_expired_memory_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

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
}

#[tokio::test(flavor = "multi_thread")]
async fn test_get_by_tag_with_expired_memories() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_expired_memory_by_tag_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

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
}

#[tokio::test(flavor = "multi_thread")]
async fn search_test_text_with_expired_memories() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_expired_search_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

        let common_tag = String::from("expired_search_tag");
        let model_signature = "test_model_expired".to_string();
        let embedding_values = vec![1.0, 0.0, 0.0];

        // Memory 1: Expired (timestamp in the past)
        let expired_memory_id = "memory_expired".to_string();
        let past_time =
            std::time::SystemTime::now().checked_sub(std::time::Duration::from_secs(3600)).unwrap(); // 1 hour ago
        let expiration_timestamp = Some(system_time_to_timestamp(past_time));
        let expired_memory = Memory {
            id: expired_memory_id.clone(),
            tags: vec![common_tag.clone()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "expired_view".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: embedding_values.clone(),
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp,
            ..Default::default()
        };
        client.add_memory(expired_memory).await.unwrap();

        // Memory 2: Non-expired (timestamp in the future)
        let non_expired_memory_id = "memory_non_expired".to_string();
        let future_time =
            std::time::SystemTime::now().checked_add(std::time::Duration::from_secs(3600)).unwrap(); // 1 hour in future
        let non_expiration_timestamp = Some(system_time_to_timestamp(future_time));
        let non_expired_memory = Memory {
            id: non_expired_memory_id.clone(),
            tags: vec![common_tag.clone()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "non_expired_view".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: embedding_values.clone(),
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp: non_expiration_timestamp,
            ..Default::default()
        };
        client.add_memory(non_expired_memory).await.unwrap();

        // Memory 3: Never-expired (no timestamp)
        let never_expired_memory_id = "memory_never_expired".to_string();
        let never_expired_memory = Memory {
            id: never_expired_memory_id.clone(),
            tags: vec![common_tag.clone()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "never_expired_view".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: embedding_values.clone(),
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp: None,
            ..Default::default()
        };
        client.add_memory(never_expired_memory).await.unwrap();

        // Perform a text search for the common tag
        let text_query = TextQuery {
            field: MemoryField::Tags as i32,
            match_type: MatchType::Equal as i32,
            value: Some(text_query::Value::StringVal(common_tag.clone())),
        };
        let query = SearchMemoryQuery {
            clause: Some(
                sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::TextQuery(
                    text_query,
                ),
            ),
        };
        let response = client.search_memory(query, 10, None, "", false).await.unwrap();

        // Collect the IDs of the memories returned
        let returned_ids: HashSet<String> =
            response.results.into_iter().map(|r| r.memory.unwrap().id).collect();

        // Assert that the expired memory is NOT in the results
        assert!(!returned_ids.contains(&expired_memory_id));

        // Assert that the non-expired and never-expired memories ARE in the results
        assert!(returned_ids.contains(&non_expired_memory_id));
        assert!(returned_ids.contains(&never_expired_memory_id));
        assert_eq!(returned_ids.len(), 2);
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn search_test_embedding_with_expired_memories() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_client_expired_embedding_search_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

        let common_tag = String::from("expired_embedding_search_tag");
        let model_signature = "test_model_expired_embedding".to_string();
        let embedding_values = vec![1.0, 0.0, 0.0];

        // Memory 1: Expired (timestamp in the past)
        let expired_memory_id = "embedding_memory_expired".to_string();
        let past_time =
            std::time::SystemTime::now().checked_sub(std::time::Duration::from_secs(3600)).unwrap(); // 1 hour ago
        let expiration_timestamp = Some(system_time_to_timestamp(past_time));
        let expired_memory = Memory {
            id: expired_memory_id.clone(),
            tags: vec![common_tag.clone()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "expired_embedding_view".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: embedding_values.clone(),
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp,
            ..Default::default()
        };
        client.add_memory(expired_memory).await.unwrap();

        // Memory 2: Non-expired (timestamp in the future)
        let non_expired_memory_id = "embedding_memory_non_expired".to_string();
        let future_time =
            std::time::SystemTime::now().checked_add(std::time::Duration::from_secs(3600)).unwrap(); // 1 hour in future
        let non_expiration_timestamp = Some(system_time_to_timestamp(future_time));
        let non_expired_memory = Memory {
            id: non_expired_memory_id.clone(),
            tags: vec![common_tag.clone()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "non_expired_embedding_view".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: embedding_values.clone(),
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp: non_expiration_timestamp,
            ..Default::default()
        };
        client.add_memory(non_expired_memory).await.unwrap();

        // Memory 3: Never-expired (no timestamp)
        let never_expired_memory_id = "embedding_memory_never_expired".to_string();
        let never_expired_memory = Memory {
            id: never_expired_memory_id.clone(),
            tags: vec![common_tag.clone()],
            views: Some(LlmViews {
                llm_views: vec![LlmView {
                    id: "never_expired_embedding_view".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: embedding_values.clone(),
                    }),
                    ..Default::default()
                }],
            }),
            expiration_timestamp: None,
            ..Default::default()
        };
        client.add_memory(never_expired_memory).await.unwrap();

        // Perform an embedding search
        let embedding_query = SearchMemoryQuery {
            clause: Some(
                sealed_memory_rust_proto::oak::private_memory::search_memory_query::Clause::EmbeddingQuery(
                    EmbeddingQuery {
                        embedding: vec![Embedding {
                            model_signature: model_signature.clone(),
                            values: embedding_values.clone(),
                        }],
                        ..Default::default()
                    },
                ),
            ),
        };
        let response = client.search_memory(embedding_query, 10, None, "", false).await.unwrap();

        // Collect the IDs of the memories returned
        let returned_ids: HashSet<String> =
            response.results.into_iter().map(|r| r.memory.unwrap().id).collect();

        // Assert that the expired memory is NOT in the results
        assert!(!returned_ids.contains(&expired_memory_id));

        // Assert that the non-expired and never-expired memories ARE in the results
        assert!(returned_ids.contains(&non_expired_memory_id));
        assert!(returned_ids.contains(&never_expired_memory_id));
        assert_eq!(returned_ids.len(), 2);
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_get_memories_by_id() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_get_memories_by_id_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

        // Add three memories
        let memory1 = Memory {
            id: "memory1".to_string(),
            tags: vec!["tag1".to_string()],
            ..Default::default()
        };
        let memory2 = Memory {
            id: "memory2".to_string(),
            tags: vec!["tag2".to_string()],
            ..Default::default()
        };
        let memory3 = Memory {
            id: "memory3".to_string(),
            tags: vec!["tag3".to_string()],
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
        let returned_ids: HashSet<String> =
            response.memories.iter().map(|m| m.id.clone()).collect();
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
        let returned_ids: HashSet<String> =
            response.memories.iter().map(|m| m.id.clone()).collect();
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
}
