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
    net::{IpAddr, Ipv4Addr, SocketAddr},
};

use anyhow::Result;
use client::{PrivateMemoryClient, SerializationFormat};
use private_memory_server_lib::{
    app,
    app::{run_persistence_service, ApplicationConfig},
};
use sealed_memory_rust_proto::{
    oak::private_memory::{text_query, LlmView, MatchType, MemoryViews, TextQuery},
    prelude::v1::*,
};
use tokio::net::TcpListener;

static TEST_EK: &[u8; 32] = b"aaaabbbbccccddddeeeeffffgggghhhh";

async fn start_server() -> Result<(
    SocketAddr,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<Result<()>>,
    tokio::task::JoinHandle<()>,
)> {
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let listener = TcpListener::bind(addr).await?;
    let addr = listener.local_addr()?;

    let db_addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let db_listener = TcpListener::bind(db_addr).await?;
    let db_addr = db_listener.local_addr()?;

    let application_config = ApplicationConfig { database_service_host: db_addr };

    let metrics = private_memory_server_lib::metrics::get_global_metrics();
    let (persistence_tx, persistence_rx) = tokio::sync::mpsc::unbounded_channel();
    let persistence_join_handle = tokio::spawn(run_persistence_service(persistence_rx));
    Ok((
        addr,
        tokio::spawn(app::service::create(listener, application_config, metrics, persistence_tx)),
        tokio::spawn(private_memory_test_database_server_lib::service::create(db_listener)),
        persistence_join_handle,
    ))
}

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

        let memory_id = "test_memory_id";
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
                views: Some(MemoryViews {
                    llm_views: vec![LlmView {
                        id: format!("view_{}", i),
                        embedding: Some(Embedding {
                            identifier: "test_model".to_string(),
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
                            identifier: "test_model".to_string(),
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
            let response =
                client.search_memory(query.clone(), 5, None, &next_page_token).await.unwrap();
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
