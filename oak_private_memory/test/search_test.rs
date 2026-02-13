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

use googletest::prelude::*;
use oak_private_memory_database::icing::{IcingMetaDatabase, IcingTempDir, PageToken};
use prost_types::Timestamp;
use sealed_memory_rust_proto::{
    oak::private_memory::{
        EmbeddingQuery, LlmView, LlmViews, MatchType, MemoryField, QueryClauses, QueryOperator,
        SearchMemoryQuery, TextQuery, search_memory_query, text_query,
    },
    prelude::v1::*,
};

#[gtest]
fn test_embedding_search_returns_scores() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("embedding-search-test"))?;

    // Add memories with different embeddings
    let memory1 = Memory {
        id: "memory1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view1".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![1.0, 2.0, 3.0],
                }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "memory2".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view2".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![4.0, 5.0, 6.0],
                }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    // Query for memories with an embedding that is closer to memory2
    let embedding_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
            embedding: vec![Embedding {
                model_signature: "test_model".to_string(),
                values: vec![1.0, 1.0, 1.0],
            }],
            ..Default::default()
        })),
    };

    let (results, _) = icing_database.search(&embedding_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();
    assert_that!(scores, not(is_empty()));
    assert_that!(scores.len(), eq(blob_ids.len()));
    assert_that!(scores, each(predicate(|&x| x > 0.0)));
    assert_that!(scores[0], eq(15.0));
    assert_that!(scores[1], eq(6.0));
    assert_that!(blob_ids, unordered_elements_are![eq(&"blob1"), eq(&"blob2")]);
    Ok(())
}

#[gtest]
fn test_hybrid_search_with_timestamp() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("embedding-search-test"))?;

    // Add memories with different embeddings and timestamps
    let memory1 = Memory {
        id: "memory1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view1".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![1.0, 2.0, 3.0],
                }),
                ..Default::default()
            }],
        }),
        event_timestamp: Some(Timestamp { seconds: 100, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "memory2".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view2".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![1.1, 2.1, 3.1],
                }),
                ..Default::default()
            }],
        }),
        event_timestamp: Some(Timestamp { seconds: 200, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    // Query for memories with an embedding and a timestamp range.
    let embedding_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
            embedding: vec![Embedding {
                model_signature: "test_model".to_string(),
                values: vec![1.0, 2.0, 3.0],
            }],
            ..Default::default()
        })),
    };

    let timestamp_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            match_type: MatchType::Gte as i32,
            field: MemoryField::EventTimestamp as i32,
            value: Some(
                sealed_memory_rust_proto::oak::private_memory::text_query::Value::TimestampVal(
                    Timestamp { seconds: 150, nanos: 0 },
                ),
            ),
        })),
    };

    let hybrid_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::And as i32,
            clauses: vec![embedding_query, timestamp_query],
        })),
    };

    let (results, _) = icing_database.search(&hybrid_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    assert_that!(blob_ids, unordered_elements_are![eq(&"blob2")]);
    assert_that!(blob_ids.len(), eq(1));

    Ok(())
}

// Regression test: when embedding search is involved in hybrid queries,
// both clause orderings should sort by embedding similarity:
//   - tag AND embedding -> sorts by embedding
//   - embedding AND tag -> sorts by embedding
// Previously, the last clause's scoring spec would win, causing
// `embedding AND tag` to incorrectly sort by CreationTimestamp.
#[gtest]
fn test_hybrid_search_clause_order_does_not_affect_ranking() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("hybrid-order-test"))?;

    // Add memories with embeddings that have different similarity scores to the
    // query. memory1 has higher similarity (1.0+2.0+3.0=6.0) than memory2
    // (0.1+0.2+0.3=0.6).
    let memory1 = Memory {
        id: "memory1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view1".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![1.0, 2.0, 3.0],
                }),
                ..Default::default()
            }],
        }),
        tags: vec!["test_tag".to_string()],
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "memory2".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view2".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![0.1, 0.2, 0.3],
                }),
                ..Default::default()
            }],
        }),
        tags: vec!["test_tag".to_string()],
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    let embedding_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
            embedding: vec![Embedding {
                model_signature: "test_model".to_string(),
                values: vec![1.0, 1.0, 1.0],
            }],
            ..Default::default()
        })),
    };

    let tag_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            match_type: MatchType::Equal as i32,
            field: MemoryField::Tags as i32,
            value: Some(text_query::Value::StringVal("test_tag".to_string())),
        })),
    };

    // Test order 1: embedding AND tag
    let query_embedding_first = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::And as i32,
            clauses: vec![embedding_query.clone(), tag_query.clone()],
        })),
    };

    // Test order 2: tag AND embedding (this was buggy before the fix)
    let query_tag_first = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::And as i32,
            clauses: vec![tag_query, embedding_query],
        })),
    };

    let (results1, _) = icing_database.search(&query_embedding_first, 10, PageToken::Start)?;
    let (results2, _) = icing_database.search(&query_tag_first, 10, PageToken::Start)?;

    // Both should return the same results in the same order (sorted by embedding
    // similarity).
    let blob_ids1: Vec<String> = results1.items.iter().map(|r| r.blob_id.clone()).collect();
    let blob_ids2: Vec<String> = results2.items.iter().map(|r| r.blob_id.clone()).collect();

    // memory1 (blob1) has higher embedding similarity, so it should come first.
    assert_that!(blob_ids1, elements_are![eq(&"blob1"), eq(&"blob2")]);
    assert_that!(blob_ids2, elements_are![eq(&"blob1"), eq(&"blob2")]);

    // Verify scores are the same regardless of order.
    let scores1: Vec<f32> = results1.items.iter().map(|r| r.score).collect();
    let scores2: Vec<f32> = results2.items.iter().map(|r| r.score).collect();
    assert_that!(scores1, eq(&scores2));

    Ok(())
}

// Test nested clauses: { TAG AND { TAG AND EMBEDDING } }
// Embedding is in a nested inner clause; should still sort by embedding.
#[gtest]
fn test_hybrid_search_nested_embedding_inner() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("nested-inner-test"))?;

    // memory1 has higher embedding similarity (1.0+2.0+3.0=6.0)
    let memory1 = Memory {
        id: "memory1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view1".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![1.0, 2.0, 3.0],
                }),
                ..Default::default()
            }],
        }),
        tags: vec!["tag1".to_string(), "tag2".to_string()],
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    // memory2 has lower embedding similarity (0.1+0.2+0.3=0.6)
    let memory2 = Memory {
        id: "memory2".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view2".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![0.1, 0.2, 0.3],
                }),
                ..Default::default()
            }],
        }),
        tags: vec!["tag1".to_string(), "tag2".to_string()],
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    let embedding_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
            embedding: vec![Embedding {
                model_signature: "test_model".to_string(),
                values: vec![1.0, 1.0, 1.0],
            }],
            ..Default::default()
        })),
    };

    let tag1_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            match_type: MatchType::Equal as i32,
            field: MemoryField::Tags as i32,
            value: Some(text_query::Value::StringVal("tag1".to_string())),
        })),
    };

    let tag2_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            match_type: MatchType::Equal as i32,
            field: MemoryField::Tags as i32,
            value: Some(text_query::Value::StringVal("tag2".to_string())),
        })),
    };

    // Build: { TAG1 AND { TAG2 AND EMBEDDING } }
    let inner_clause = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::And as i32,
            clauses: vec![tag2_query, embedding_query],
        })),
    };
    let outer_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::And as i32,
            clauses: vec![tag1_query, inner_clause],
        })),
    };

    let (results, _) = icing_database.search(&outer_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();

    // Should be sorted by embedding similarity (blob1 first).
    assert_that!(blob_ids, elements_are![eq(&"blob1"), eq(&"blob2")]);

    Ok(())
}

// Test nested clauses: { { TAG AND EMBEDDING } AND TAG }
// Embedding is in a nested inner clause with outer tag after.
#[gtest]
fn test_hybrid_search_nested_embedding_outer_tag() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("nested-outer-test"))?;

    // memory1 has higher embedding similarity
    let memory1 = Memory {
        id: "memory1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view1".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![1.0, 2.0, 3.0],
                }),
                ..Default::default()
            }],
        }),
        tags: vec!["tag1".to_string(), "tag2".to_string()],
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    // memory2 has lower embedding similarity
    let memory2 = Memory {
        id: "memory2".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view2".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![0.1, 0.2, 0.3],
                }),
                ..Default::default()
            }],
        }),
        tags: vec!["tag1".to_string(), "tag2".to_string()],
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    let embedding_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
            embedding: vec![Embedding {
                model_signature: "test_model".to_string(),
                values: vec![1.0, 1.0, 1.0],
            }],
            ..Default::default()
        })),
    };

    let tag1_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            match_type: MatchType::Equal as i32,
            field: MemoryField::Tags as i32,
            value: Some(text_query::Value::StringVal("tag1".to_string())),
        })),
    };

    let tag2_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            match_type: MatchType::Equal as i32,
            field: MemoryField::Tags as i32,
            value: Some(text_query::Value::StringVal("tag2".to_string())),
        })),
    };

    // Build: { { TAG1 AND EMBEDDING } AND TAG2 }
    let inner_clause = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::And as i32,
            clauses: vec![tag1_query, embedding_query],
        })),
    };
    let outer_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::And as i32,
            clauses: vec![inner_clause, tag2_query],
        })),
    };

    let (results, _) = icing_database.search(&outer_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();

    // Should be sorted by embedding similarity (blob1 first).
    assert_that!(blob_ids, elements_are![eq(&"blob1"), eq(&"blob2")]);

    Ok(())
}

#[gtest]
fn test_search_views() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("embedding-search-test"))?;

    // Add memories with different embeddings and timestamps
    let memory1 = Memory {
        id: "memory1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view1".to_string(),
                embedding: Some(Embedding {
                    model_signature: "test_model".to_string(),
                    values: vec![1.0, 1.0, 1.0],
                }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "memory1".to_string())?;
    let memory2 = Memory { id: "memory2".to_string(), ..Default::default() };
    icing_database.add_memory(&memory2, "memory2".to_string())?;

    // Query for memories with an embedding and a timestamp range.
    let embedding_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
            embedding: vec![Embedding {
                model_signature: "test_model".to_string(),
                values: vec![1.0, 1.0, 1.0],
            }],
            ..Default::default()
        })),
    };

    let (results, _) = icing_database.search(&embedding_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();
    assert_that!(blob_ids, unordered_elements_are![eq("memory1")]);
    assert_that!(scores, unordered_elements_are![eq(&3.0)]);

    Ok(())
}

#[gtest]
fn test_text_search_timestamp_filtering() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("text-search-test"))?;

    // Add memories with different timestamps
    let memory1 = Memory {
        id: "memory1".to_string(),
        created_timestamp: Some(Timestamp { seconds: 100, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "memory2".to_string(),
        created_timestamp: Some(Timestamp { seconds: 200, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    let memory3 = Memory {
        id: "memory3".to_string(),
        created_timestamp: Some(Timestamp { seconds: 300, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory3, "blob3".to_string())?;

    // Test case 1: Greater than or equal to
    let gte_query = TextQuery {
        field: MemoryField::CreatedTimestamp as i32,
        match_type: MatchType::Gte as i32,
        value: Some(text_query::Value::TimestampVal(Timestamp { seconds: 200, nanos: 0 })),
    };
    let (results, _) = icing_database.text_search(&gte_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    assert_that!(blob_ids, unordered_elements_are![eq("blob2"), eq("blob3")]);

    // Test case 2: Less than
    let lt_query = TextQuery {
        field: MemoryField::CreatedTimestamp as i32,
        match_type: MatchType::Lt as i32,
        value: Some(text_query::Value::TimestampVal(Timestamp { seconds: 200, nanos: 0 })),
    };
    let (results, _) = icing_database.text_search(&lt_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    assert_that!(blob_ids, unordered_elements_are![eq("blob1")]);

    Ok(())
}

#[gtest]
fn test_text_search_id_filtering() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("text-search-test"))?;

    // Add memories with different timestamps
    let memory1 = Memory {
        id: "memory1".to_string(),
        created_timestamp: Some(Timestamp { seconds: 100, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "memory2".to_string(),
        created_timestamp: Some(Timestamp { seconds: 200, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    let memory3 = Memory {
        id: "memory3".to_string(),
        created_timestamp: Some(Timestamp { seconds: 300, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory3, "blob3".to_string())?;

    // Test case 1: Exact match
    let eq_query = TextQuery {
        field: MemoryField::Id as i32,
        match_type: MatchType::Equal as i32,
        value: Some(text_query::Value::StringVal("memory2".to_string())),
    };
    let (results, _) = icing_database.text_search(&eq_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    assert_that!(blob_ids, unordered_elements_are![eq("blob2")]);

    Ok(())
}

#[gtest]
fn test_query_clauses_and_operator() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("text-search-test"))?;

    // Add memories with different timestamps and tags
    let memory1 = Memory {
        id: "memory1".to_string(),
        tags: vec!["tag1".to_string()],
        created_timestamp: Some(Timestamp { seconds: 100, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "memory2".to_string(),
        tags: vec!["tag1".to_string(), "tag2".to_string()],
        created_timestamp: Some(Timestamp { seconds: 200, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    let memory3 = Memory {
        id: "memory3".to_string(),
        tags: vec!["tag2".to_string()],
        created_timestamp: Some(Timestamp { seconds: 300, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory3, "blob3".to_string())?;

    // Query for memories with "tag1" AND timestamp >= 200
    let tag_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            field: MemoryField::Tags as i32,
            match_type: MatchType::Equal as i32,
            value: Some(text_query::Value::StringVal("tag1".to_string())),
        })),
    };
    let timestamp_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            field: MemoryField::CreatedTimestamp as i32,
            match_type: MatchType::Gte as i32,
            value: Some(text_query::Value::TimestampVal(Timestamp { seconds: 200, nanos: 0 })),
        })),
    };
    let and_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::And as i32,
            clauses: vec![tag_query, timestamp_query],
        })),
    };

    let (results, _) = icing_database.search(&and_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    assert_that!(blob_ids, unordered_elements_are![eq("blob2")]);

    Ok(())
}

#[gtest]
fn test_query_clauses_or_operator() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("text-search-test"))?;

    // Add memories with different timestamps and tags
    let memory1 = Memory {
        id: "memory1".to_string(),
        tags: vec!["tag1".to_string()],
        created_timestamp: Some(Timestamp { seconds: 100, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "memory2".to_string(),
        tags: vec!["tag2".to_string()],
        created_timestamp: Some(Timestamp { seconds: 200, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    let memory3 = Memory {
        id: "memory3".to_string(),
        tags: vec!["tag3".to_string()],
        created_timestamp: Some(Timestamp { seconds: 300, nanos: 0 }),
        ..Default::default()
    };
    icing_database.add_memory(&memory3, "blob3".to_string())?;

    // Query for memories with "tag1" OR timestamp >= 300
    let tag_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            field: MemoryField::Tags as i32,
            match_type: MatchType::Equal as i32,
            value: Some(text_query::Value::StringVal("tag1".to_string())),
        })),
    };
    let timestamp_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            field: MemoryField::CreatedTimestamp as i32,
            match_type: MatchType::Gte as i32,
            value: Some(text_query::Value::TimestampVal(Timestamp { seconds: 300, nanos: 0 })),
        })),
    };
    let or_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::Or as i32,
            clauses: vec![tag_query, timestamp_query],
        })),
    };

    let (results, _) = icing_database.search(&or_query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    assert_that!(blob_ids, unordered_elements_are![eq("blob1"), eq("blob3")]);

    Ok(())
}

#[gtest]
fn test_search_with_pagination_returns_correct_view() -> anyhow::Result<()> {
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("embedding-search-test"))?;

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
    icing_database.add_memory(&memory1, "blob1".to_string())?;

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
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    // Query for memories with an embedding that is closer to memory2's view2b.
    let embedding_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
            embedding: vec![Embedding {
                model_signature: "test_model".to_string(),
                values: vec![1.0, 1.0, 0.0],
            }],
            ..Default::default()
        })),
    };

    let (results, _) = icing_database.search(&embedding_query, 1, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();
    assert_that!(blob_ids.len(), eq(1));
    let top_blob_id = blob_ids.first().unwrap();
    assert_that!(top_blob_id, eq("blob2"));
    assert_that!(scores[0], eq(2.0));
    let view_ids = &results.items.first().unwrap().view_ids;
    assert_that!(view_ids.len(), eq(1));
    let top_view_id = view_ids.first().unwrap();
    assert_that!(top_view_id, eq("view2b"));

    Ok(())
}
