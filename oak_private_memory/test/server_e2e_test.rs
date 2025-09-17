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

use std::{collections::HashMap, time::Duration};

use client::{PrivateMemoryClient, SerializationFormat};
use private_memory_test_utils::start_server;
use sealed_memory_rust_proto::{
    oak::private_memory::{memory_value, text_query, MatchType, TextQuery},
    prelude::v1::*,
};
use tokio::time::sleep;

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

#[tokio::test(flavor = "multi_thread")]
async fn test_add_get_reset_memory_all_modes() {
    let (addr, _db_addr, _server_join_handle, _db_join_handle) = start_server().await.unwrap();
    let url = format!("http://{addr}");
    let pm_uid = "test_add_get_reset_user";

    for &format in [SerializationFormat::BinaryProto, SerializationFormat::Json].iter() {
        let mut client =
            PrivateMemoryClient::create_with_start_session(&url, pm_uid, TEST_EK, format)
                .await
                .unwrap();

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
            MemoryValue {
                value: Some(memory_value::Value::Int64Val(123456789)),
                ..Default::default()
            },
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
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_standalone_text_query() {
    let (addr, _server_join_handle, _db_join_handle, _persistence_join_handle) =
        start_server().await.unwrap();
    let url = format!("http://{}", addr);
    let pm_uid = "test_standalone_text_query_user";

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
        let response = client.search_memory(query, 10, None, "").await.unwrap();
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
        let response = client.search_memory(query, 10, None, "").await.unwrap();
        assert_eq!(response.results.len(), 1);
        assert_eq!(response.results[0].memory.as_ref().unwrap().id, "memory1");
    }
}
