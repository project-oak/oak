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
        SearchMemoryQuery, TextQuery, search_memories_filter::Value as FilterValue,
        search_memories_sort::Sort as SortValue, search_memory_query, text_query,
    },
    prelude::v1::*,
};

// =============================================================================
// Test helpers — Memory builders
// =============================================================================

/// Shorthand for `Some(Timestamp { seconds, nanos: 0 })`.
fn ts(seconds: i64) -> Option<Timestamp> {
    Some(Timestamp { seconds, nanos: 0 })
}

/// Creates a single `LlmView` with a "test_model" embedding.
fn llm_view(id: &str, values: &[f32]) -> LlmView {
    LlmView {
        id: id.to_string(),
        embedding: Some(Embedding {
            model_signature: "test_model".to_string(),
            values: values.to_vec(),
        }),
        ..Default::default()
    }
}

/// Creates a `Memory` with a single embedding view.
fn mem_embedded(id: &str, values: &[f32]) -> Memory {
    Memory {
        id: id.to_string(),
        views: Some(LlmViews { llm_views: vec![llm_view(&format!("{id}_view"), values)] }),
        ..Default::default()
    }
}

/// Creates a `Memory` with tags.
fn mem_tagged(id: &str, tags: &[&str]) -> Memory {
    Memory {
        id: id.to_string(),
        tags: tags.iter().map(|t| t.to_string()).collect(),
        ..Default::default()
    }
}

// =============================================================================
// Test helpers — v1 query clause builders (SearchMemoryQuery)
// =============================================================================

/// Builds an embedding search clause with "test_model".
fn embedding_clause(values: &[f32]) -> SearchMemoryQuery {
    SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
            embedding: vec![Embedding {
                model_signature: "test_model".to_string(),
                values: values.to_vec(),
            }],
            ..Default::default()
        })),
    }
}

/// Builds a tag equality clause.
fn tag_clause(tag: &str) -> SearchMemoryQuery {
    SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            match_type: MatchType::Equal as i32,
            field: MemoryField::Tags as i32,
            value: Some(text_query::Value::StringVal(tag.to_string())),
        })),
    }
}

/// Builds a timestamp comparison clause.
fn ts_clause(field: MemoryField, match_type: MatchType, seconds: i64) -> SearchMemoryQuery {
    SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::TextQuery(TextQuery {
            match_type: match_type as i32,
            field: field as i32,
            value: Some(text_query::Value::TimestampVal(Timestamp { seconds, nanos: 0 })),
        })),
    }
}

/// Combines clauses with AND.
fn and_q(clauses: Vec<SearchMemoryQuery>) -> SearchMemoryQuery {
    SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::And as i32,
            clauses,
        })),
    }
}

/// Combines clauses with OR.
fn or_q(clauses: Vec<SearchMemoryQuery>) -> SearchMemoryQuery {
    SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::QueryClauses(QueryClauses {
            query_operator: QueryOperator::Or as i32,
            clauses,
        })),
    }
}

/// Runs a v1 `search()` and returns blob IDs in result order.
fn query_blob_ids(
    db: &IcingMetaDatabase,
    query: &SearchMemoryQuery,
    limit: i32,
) -> anyhow::Result<Vec<String>> {
    let (results, _) = db.search(query, limit, PageToken::Start)?;
    Ok(results.items.iter().map(|r| r.blob_id.clone()).collect())
}

/// Builds a TextQuery for timestamp comparisons (used with `text_search`).
fn text_ts_query(field: MemoryField, match_type: MatchType, seconds: i64) -> TextQuery {
    TextQuery {
        field: field as i32,
        match_type: match_type as i32,
        value: Some(text_query::Value::TimestampVal(Timestamp { seconds, nanos: 0 })),
    }
}

/// Runs `text_search()` and returns blob IDs in result order.
fn text_search_blob_ids(
    db: &IcingMetaDatabase,
    query: &TextQuery,
    limit: i32,
) -> anyhow::Result<Vec<String>> {
    let (results, _) = db.text_search(query, limit, PageToken::Start)?;
    Ok(results.items.iter().map(|r| r.blob_id.clone()).collect())
}

// =============================================================================
// Test helpers — v2 filter builders (SearchMemoriesFilter /
// SearchMemoriesRequest)
// =============================================================================

fn tag_filter(tag: &str) -> SearchMemoriesFilter {
    SearchMemoriesFilter {
        value: Some(FilterValue::TagsFilter(StringFilter { value: tag.to_string() })),
    }
}

fn id_filter(id: &str) -> SearchMemoriesFilter {
    SearchMemoriesFilter {
        value: Some(FilterValue::IdFilter(StringFilter { value: id.to_string() })),
    }
}

fn name_filter(name: &str) -> SearchMemoriesFilter {
    SearchMemoriesFilter {
        value: Some(FilterValue::NameFilter(StringFilter { value: name.to_string() })),
    }
}

fn created_ts_filter(cmp: ComparisonType, seconds: i64) -> SearchMemoriesFilter {
    SearchMemoriesFilter {
        value: Some(FilterValue::CreatedTimestampFilter(TimeFilter {
            comparison: cmp as i32,
            value: Some(Timestamp { seconds, nanos: 0 }),
        })),
    }
}

fn event_ts_filter(cmp: ComparisonType, seconds: i64) -> SearchMemoriesFilter {
    SearchMemoriesFilter {
        value: Some(FilterValue::EventTimestampFilter(TimeFilter {
            comparison: cmp as i32,
            value: Some(Timestamp { seconds, nanos: 0 }),
        })),
    }
}

fn and_filter(filters: Vec<SearchMemoriesFilter>) -> SearchMemoriesFilter {
    SearchMemoriesFilter {
        value: Some(FilterValue::AndOperator(SearchMemoriesFilters { filters })),
    }
}

fn or_filter(filters: Vec<SearchMemoriesFilter>) -> SearchMemoriesFilter {
    SearchMemoriesFilter { value: Some(FilterValue::OrOperator(SearchMemoriesFilters { filters })) }
}

fn not_filter(inner: SearchMemoriesFilter) -> SearchMemoriesFilter {
    SearchMemoriesFilter { value: Some(FilterValue::NotOperator(Box::new(inner))) }
}

fn filter_request(filter: SearchMemoriesFilter, page_size: i32) -> SearchMemoriesRequest {
    SearchMemoriesRequest { filter: Some(filter), page_size, ..Default::default() }
}

/// Build a `SearchMemoriesRequest` with both a filter and a sort spec.
fn sorted_request(filter: SearchMemoriesFilter, sort: SortValue) -> SearchMemoriesRequest {
    SearchMemoriesRequest {
        filter: Some(filter),
        sort: vec![SearchMemoriesSort { sort: Some(sort) }],
        page_size: 10,
        ..Default::default()
    }
}

/// Execute `search_memories` and return the blob IDs in result order.
fn search_blob_ids(
    db: &IcingMetaDatabase,
    request: &SearchMemoriesRequest,
) -> anyhow::Result<Vec<String>> {
    let (results, _) = db.search_memories(request)?;
    Ok(results.items.iter().map(|r| r.blob_id.clone()).collect())
}

// =============================================================================
// v1 Search API tests
// =============================================================================

#[gtest]
fn test_embedding_search_returns_scores() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("embedding-search-test"))?;
    db.add_memory(&mem_embedded("memory1", &[1.0, 2.0, 3.0]), "blob1".into())?;
    db.add_memory(&mem_embedded("memory2", &[4.0, 5.0, 6.0]), "blob2".into())?;

    let query = embedding_clause(&[1.0, 1.0, 1.0]);
    let (results, _) = db.search(&query, 10, PageToken::Start)?;
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
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("embedding-search-test"))?;

    let mut m1 = mem_embedded("memory1", &[1.0, 2.0, 3.0]);
    m1.event_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_embedded("memory2", &[1.1, 2.1, 3.1]);
    m2.event_timestamp = ts(200);
    db.add_memory(&m2, "blob2".into())?;

    // embedding [1,2,3] AND event_timestamp >= 150 → only blob2.
    let query = and_q(vec![
        embedding_clause(&[1.0, 2.0, 3.0]),
        ts_clause(MemoryField::EventTimestamp, MatchType::Gte, 150),
    ]);
    let blob_ids = query_blob_ids(&db, &query, 10)?;
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
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("hybrid-order-test"))?;

    // memory1 has higher similarity (1+2+3=6) than memory2 (0.1+0.2+0.3=0.6).
    let mut m1 = mem_embedded("memory1", &[1.0, 2.0, 3.0]);
    m1.tags = vec!["test_tag".into()];
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_embedded("memory2", &[0.1, 0.2, 0.3]);
    m2.tags = vec!["test_tag".into()];
    db.add_memory(&m2, "blob2".into())?;

    let emb = embedding_clause(&[1.0, 1.0, 1.0]);
    let tag = tag_clause("test_tag");

    // Order 1: embedding AND tag
    let query1 = and_q(vec![emb.clone(), tag.clone()]);
    // Order 2: tag AND embedding (was buggy before the fix)
    let query2 = and_q(vec![tag, emb]);

    let (results1, _) = db.search(&query1, 10, PageToken::Start)?;
    let (results2, _) = db.search(&query2, 10, PageToken::Start)?;

    // Both should return the same results sorted by embedding similarity.
    let ids1: Vec<String> = results1.items.iter().map(|r| r.blob_id.clone()).collect();
    let ids2: Vec<String> = results2.items.iter().map(|r| r.blob_id.clone()).collect();
    assert_that!(ids1, elements_are![eq(&"blob1"), eq(&"blob2")]);
    assert_that!(ids2, elements_are![eq(&"blob1"), eq(&"blob2")]);

    let scores1: Vec<f32> = results1.items.iter().map(|r| r.score).collect();
    let scores2: Vec<f32> = results2.items.iter().map(|r| r.score).collect();
    assert_that!(scores1, eq(&scores2));

    Ok(())
}

// Test nested clauses: { TAG AND { TAG AND EMBEDDING } }
// Embedding is in a nested inner clause; should still sort by embedding.
#[gtest]
fn test_hybrid_search_nested_embedding_inner() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("nested-inner-test"))?;

    let mut m1 = mem_embedded("memory1", &[1.0, 2.0, 3.0]);
    m1.tags = vec!["tag1".into(), "tag2".into()];
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_embedded("memory2", &[0.1, 0.2, 0.3]);
    m2.tags = vec!["tag1".into(), "tag2".into()];
    db.add_memory(&m2, "blob2".into())?;

    // { tag1 AND { tag2 AND embedding[1,1,1] } }
    let inner = and_q(vec![tag_clause("tag2"), embedding_clause(&[1.0, 1.0, 1.0])]);
    let outer = and_q(vec![tag_clause("tag1"), inner]);

    // Should be sorted by embedding similarity (blob1 first).
    assert_that!(query_blob_ids(&db, &outer, 10)?, elements_are![eq(&"blob1"), eq(&"blob2")]);
    Ok(())
}

// Test nested clauses: { { TAG AND EMBEDDING } AND TAG }
// Embedding is in a nested inner clause with outer tag after.
#[gtest]
fn test_hybrid_search_nested_embedding_outer_tag() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("nested-outer-test"))?;

    let mut m1 = mem_embedded("memory1", &[1.0, 2.0, 3.0]);
    m1.tags = vec!["tag1".into(), "tag2".into()];
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_embedded("memory2", &[0.1, 0.2, 0.3]);
    m2.tags = vec!["tag1".into(), "tag2".into()];
    db.add_memory(&m2, "blob2".into())?;

    // { { tag1 AND embedding[1,1,1] } AND tag2 }
    let inner = and_q(vec![tag_clause("tag1"), embedding_clause(&[1.0, 1.0, 1.0])]);
    let outer = and_q(vec![inner, tag_clause("tag2")]);

    assert_that!(query_blob_ids(&db, &outer, 10)?, elements_are![eq(&"blob1"), eq(&"blob2")]);
    Ok(())
}

#[gtest]
fn test_search_views() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("embedding-search-test"))?;
    db.add_memory(&mem_embedded("memory1", &[1.0, 1.0, 1.0]), "memory1".into())?;
    db.add_memory(&Memory { id: "memory2".into(), ..Default::default() }, "memory2".into())?;

    let query = embedding_clause(&[1.0, 1.0, 1.0]);
    let (results, _) = db.search(&query, 10, PageToken::Start)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();
    let scores: Vec<f32> = results.items.iter().map(|r| r.score).collect();
    assert_that!(blob_ids, unordered_elements_are![eq("memory1")]);
    assert_that!(scores, unordered_elements_are![eq(&3.0)]);

    Ok(())
}

#[gtest]
fn test_text_search_timestamp_filtering() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("text-search-test"))?;
    for (id, blob, secs) in
        [("memory1", "blob1", 100), ("memory2", "blob2", 200), ("memory3", "blob3", 300)]
    {
        let m = Memory { id: id.into(), created_timestamp: ts(secs), ..Default::default() };
        db.add_memory(&m, blob.into())?;
    }

    // GTE 200 → blob2, blob3
    let gte = text_ts_query(MemoryField::CreatedTimestamp, MatchType::Gte, 200);
    assert_that!(
        text_search_blob_ids(&db, &gte, 10)?,
        unordered_elements_are![eq("blob2"), eq("blob3")]
    );

    // LT 200 → blob1
    let lt = text_ts_query(MemoryField::CreatedTimestamp, MatchType::Lt, 200);
    assert_that!(text_search_blob_ids(&db, &lt, 10)?, unordered_elements_are![eq("blob1")]);

    Ok(())
}

#[gtest]
fn test_text_search_id_filtering() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("text-search-test"))?;
    for (id, blob, secs) in
        [("memory1", "blob1", 100), ("memory2", "blob2", 200), ("memory3", "blob3", 300)]
    {
        let m = Memory { id: id.into(), created_timestamp: ts(secs), ..Default::default() };
        db.add_memory(&m, blob.into())?;
    }

    let eq_query = TextQuery {
        field: MemoryField::Id as i32,
        match_type: MatchType::Equal as i32,
        value: Some(text_query::Value::StringVal("memory2".into())),
    };
    assert_that!(text_search_blob_ids(&db, &eq_query, 10)?, unordered_elements_are![eq("blob2")]);

    Ok(())
}

#[gtest]
fn test_query_clauses_and_operator() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("text-search-test"))?;

    let mut m1 = mem_tagged("memory1", &["tag1"]);
    m1.created_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_tagged("memory2", &["tag1", "tag2"]);
    m2.created_timestamp = ts(200);
    db.add_memory(&m2, "blob2".into())?;

    let mut m3 = mem_tagged("memory3", &["tag2"]);
    m3.created_timestamp = ts(300);
    db.add_memory(&m3, "blob3".into())?;

    // tag1 AND created_timestamp >= 200 → blob2
    let query = and_q(vec![
        tag_clause("tag1"),
        ts_clause(MemoryField::CreatedTimestamp, MatchType::Gte, 200),
    ]);
    assert_that!(query_blob_ids(&db, &query, 10)?, unordered_elements_are![eq("blob2")]);

    Ok(())
}

#[gtest]
fn test_query_clauses_or_operator() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("text-search-test"))?;

    let mut m1 = mem_tagged("memory1", &["tag1"]);
    m1.created_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_tagged("memory2", &["tag2"]);
    m2.created_timestamp = ts(200);
    db.add_memory(&m2, "blob2".into())?;

    let mut m3 = mem_tagged("memory3", &["tag3"]);
    m3.created_timestamp = ts(300);
    db.add_memory(&m3, "blob3".into())?;

    // tag1 OR created_timestamp >= 300 → blob1, blob3
    let query = or_q(vec![
        tag_clause("tag1"),
        ts_clause(MemoryField::CreatedTimestamp, MatchType::Gte, 300),
    ]);
    assert_that!(
        query_blob_ids(&db, &query, 10)?,
        unordered_elements_are![eq("blob1"), eq("blob3")]
    );

    Ok(())
}

#[gtest]
fn test_search_with_pagination_returns_correct_view() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("embedding-search-test"))?;

    // Memory 1 with two views.
    let memory1 = Memory {
        id: "memory1".into(),
        views: Some(LlmViews {
            llm_views: vec![
                llm_view("view1a", &[1.0, 0.0, 0.0]),
                llm_view("view1b", &[0.0, 1.0, 0.0]),
            ],
        }),
        ..Default::default()
    };
    db.add_memory(&memory1, "blob1".into())?;

    // Memory 2 with two views (view2b has the highest score).
    let memory2 = Memory {
        id: "memory2".into(),
        views: Some(LlmViews {
            llm_views: vec![
                llm_view("view2a", &[0.0, 0.0, 1.0]),
                llm_view("view2b", &[1.0, 1.0, 0.0]),
            ],
        }),
        ..Default::default()
    };
    db.add_memory(&memory2, "blob2".into())?;

    // Query closer to memory2's view2b.
    let query = embedding_clause(&[1.0, 1.0, 0.0]);
    let (results, _) = db.search(&query, 1, PageToken::Start)?;

    assert_that!(results.items.len(), eq(1));
    let top = results.items.first().unwrap();
    assert_that!(&top.blob_id, eq("blob2"));
    assert_that!(top.score, eq(2.0));
    assert_that!(top.view_ids.len(), eq(1));
    assert_that!(top.view_ids.first().unwrap(), eq("view2b"));

    Ok(())
}

/// Verify that `search()` with a tag-only text query returns memories sorted
/// by `created_timestamp` descending (newest first).
#[gtest]
fn test_search_by_tag_sorts_by_created_timestamp() -> anyhow::Result<()> {
    use sealed_memory_rust_proto::oak::private_memory::memory_value;

    let mut db = IcingMetaDatabase::new(IcingTempDir::new("tag-ts-order-test"))?;

    // Insert 5 memories in non-monotonic order to catch ordering bugs.
    let insertion_order: Vec<usize> = vec![0, 3, 1, 4, 2];
    let timestamps: Vec<i64> = vec![1000, 2000, 3000, 4000, 5000];

    for &i in &insertion_order {
        let memory = Memory {
            id: format!("ts_order_test_ts_verify_{}", i),
            tags: vec!["ts_order_test".into()],
            created_timestamp: ts(timestamps[i]),
            content: Some(MemoryContent {
                contents: std::collections::HashMap::from([(
                    "text_content".into(),
                    MemoryValue {
                        value: Some(memory_value::Value::StringVal(format!(
                            "verify_content_{}",
                            i
                        ))),
                        ..Default::default()
                    },
                )]),
            }),
            ..Default::default()
        };
        db.add_memory(&memory, format!("blob_ts_verify_{}", i))?;
    }

    let query = tag_clause("ts_order_test");
    let blob_ids = query_blob_ids(&db, &query, 100)?;

    assert_that!(blob_ids.len(), eq(5));
    // Expect newest-first: 4 (5000s), 3 (4000s), 2 (3000s), 1 (2000s), 0 (1000s)
    assert_that!(
        blob_ids,
        elements_are![
            eq("blob_ts_verify_4"),
            eq("blob_ts_verify_3"),
            eq("blob_ts_verify_2"),
            eq("blob_ts_verify_1"),
            eq("blob_ts_verify_0"),
        ]
    );

    Ok(())
}

// =============================================================================
// Search API v2: search_memories() tests
// =============================================================================

#[gtest]
fn test_search_memories_v2_tag_filter() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-tag-filter-test"))?;
    db.add_memory(&mem_tagged("m1", &["alpha", "beta"]), "blob1".into())?;
    db.add_memory(&mem_tagged("m2", &["beta", "gamma"]), "blob2".into())?;
    db.add_memory(&mem_tagged("m3", &["gamma"]), "blob3".into())?;

    // tag "beta" → m1, m2
    let req = filter_request(tag_filter("beta"), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob1"), eq("blob2")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_id_filter() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-id-filter-test"))?;
    db.add_memory(&Memory { id: "m1".into(), ..Default::default() }, "blob1".into())?;
    db.add_memory(&Memory { id: "m2".into(), ..Default::default() }, "blob2".into())?;

    let req = filter_request(id_filter("m2"), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob2")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_name_filter() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-name-filter-test"))?;
    db.add_memory(
        &Memory { id: "m1".into(), name: "grocery_list".into(), ..Default::default() },
        "blob1".into(),
    )?;
    db.add_memory(
        &Memory { id: "m2".into(), name: "todo_list".into(), ..Default::default() },
        "blob2".into(),
    )?;

    let req = filter_request(name_filter("grocery_list"), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob1")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_tag_filter_with_missing_tags() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-tag-missing-test"))?;
    db.add_memory(&mem_tagged("m1", &["alpha", "beta"]), "blob1".into())?;
    db.add_memory(&mem_tagged("m2", &["beta"]), "blob2".into())?;
    db.add_memory(&Memory { id: "m3".into(), ..Default::default() }, "blob3".into())?; // no tags

    // "beta" → m1, m2 (not m3)
    let req = filter_request(tag_filter("beta"), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob1"), eq("blob2")]);

    // "alpha" → m1 only
    let req = filter_request(tag_filter("alpha"), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob1")]);

    // "nonexistent" → empty
    let req = filter_request(tag_filter("nonexistent"), 10);
    let (results, _) = db.search_memories(&req)?;
    assert_that!(results.items, is_empty());

    Ok(())
}

#[gtest]
fn test_search_memories_v2_name_filter_with_missing_name() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-name-missing-test"))?;
    db.add_memory(
        &Memory { id: "m1".into(), name: "grocery_list".into(), ..Default::default() },
        "blob1".into(),
    )?;
    db.add_memory(&Memory { id: "m2".into(), ..Default::default() }, "blob2".into())?;

    let req = filter_request(name_filter("grocery_list"), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob1")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_timestamp_gte() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-ts-gte-test"))?;
    for (id, blob, secs) in [("m1", "blob1", 100), ("m2", "blob2", 200), ("m3", "blob3", 300)] {
        let m = Memory { id: id.into(), created_timestamp: ts(secs), ..Default::default() };
        db.add_memory(&m, blob.into())?;
    }

    // created_timestamp >= 200 → m2, m3
    let req = filter_request(created_ts_filter(ComparisonType::Gte, 200), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq(&"blob2"), eq(&"blob3")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_timestamp_lt() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-ts-lt-test"))?;
    for (id, blob, secs) in [("m1", "blob1", 100), ("m2", "blob2", 200)] {
        let m = Memory { id: id.into(), created_timestamp: ts(secs), ..Default::default() };
        db.add_memory(&m, blob.into())?;
    }

    // created_timestamp < 200 → m1 only
    let req = filter_request(created_ts_filter(ComparisonType::Lt, 200), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq(&"blob1")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_timestamp_eq() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-ts-eq-test"))?;
    for (id, blob, secs) in [("m1", "blob1", 100), ("m2", "blob2", 200)] {
        let m = Memory { id: id.into(), created_timestamp: ts(secs), ..Default::default() };
        db.add_memory(&m, blob.into())?;
    }

    // created_timestamp == 100 → m1 only
    let req = filter_request(created_ts_filter(ComparisonType::Eq, 100), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq(&"blob1")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_event_timestamp_gte_with_missing() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-evt-gte-missing-test"))?;

    let mut m1 = mem_tagged("m1", &["common"]);
    m1.event_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_tagged("m2", &["common"]);
    m2.event_timestamp = ts(300);
    db.add_memory(&m2, "blob2".into())?;

    // m3: no event_timestamp
    db.add_memory(&mem_tagged("m3", &["common"]), "blob3".into())?;

    // event_timestamp >= 200 → m2 only
    let req = filter_request(event_ts_filter(ComparisonType::Gte, 200), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq(&"blob2")]);

    // event_timestamp >= 0 → m1, m2 (not m3 which has no field)
    let req = filter_request(event_ts_filter(ComparisonType::Gte, 0), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq(&"blob1"), eq(&"blob2")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_event_timestamp_lt_with_missing() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-evt-lt-missing-test"))?;

    let mut m1 = mem_tagged("m1", &["common"]);
    m1.event_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_tagged("m2", &["common"]);
    m2.event_timestamp = ts(300);
    db.add_memory(&m2, "blob2".into())?;

    db.add_memory(&mem_tagged("m3", &["common"]), "blob3".into())?; // no event_timestamp

    // event_timestamp < 200 → m1 only (m3 excluded)
    let req = filter_request(event_ts_filter(ComparisonType::Lt, 200), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq(&"blob1")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_event_timestamp_eq_with_missing() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-evt-eq-missing-test"))?;

    let mut m1 = mem_tagged("m1", &["common"]);
    m1.event_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_tagged("m2", &["common"]);
    m2.event_timestamp = ts(100);
    db.add_memory(&m2, "blob2".into())?;

    db.add_memory(&mem_tagged("m3", &["common"]), "blob3".into())?; // no event_timestamp

    // event_timestamp == 100 → m1, m2 (m3 excluded)
    let req = filter_request(event_ts_filter(ComparisonType::Eq, 100), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq(&"blob1"), eq(&"blob2")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_and_filter() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-and-filter-test"))?;

    let mut m1 = mem_tagged("m1", &["alpha"]);
    m1.created_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_tagged("m2", &["alpha"]);
    m2.created_timestamp = ts(200);
    db.add_memory(&m2, "blob2".into())?;

    let mut m3 = mem_tagged("m3", &["beta"]);
    m3.created_timestamp = ts(300);
    db.add_memory(&m3, "blob3".into())?;

    // tag == "alpha" AND created_timestamp >= 200 → m2
    let req = filter_request(
        and_filter(vec![tag_filter("alpha"), created_ts_filter(ComparisonType::Gte, 200)]),
        10,
    );
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob2")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_or_filter() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-or-filter-test"))?;
    db.add_memory(&mem_tagged("m1", &["alpha"]), "blob1".into())?;
    db.add_memory(&mem_tagged("m2", &["beta"]), "blob2".into())?;
    db.add_memory(&mem_tagged("m3", &["gamma"]), "blob3".into())?;

    // tag == "alpha" OR tag == "gamma" → m1, m3
    let req = filter_request(or_filter(vec![tag_filter("alpha"), tag_filter("gamma")]), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob1"), eq("blob3")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_not_filter() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-not-filter-test"))?;
    db.add_memory(&mem_tagged("m1", &["alpha"]), "blob1".into())?;
    db.add_memory(&mem_tagged("m2", &["beta"]), "blob2".into())?;

    // NOT tag == "alpha" → m2
    let req = filter_request(not_filter(tag_filter("alpha")), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob2")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_nested_composite_filter() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-nested-composite"))?;

    let mut m1 = mem_tagged("m1", &["alpha"]);
    m1.created_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    let mut m2 = mem_tagged("m2", &["alpha"]);
    m2.created_timestamp = ts(200);
    db.add_memory(&m2, "blob2".into())?;

    let mut m3 = mem_tagged("m3", &["beta"]);
    m3.created_timestamp = ts(300);
    db.add_memory(&m3, "blob3".into())?;

    let mut m4 = mem_tagged("m4", &["gamma"]);
    m4.created_timestamp = ts(400);
    db.add_memory(&m4, "blob4".into())?;

    // (tag="alpha" AND created_timestamp >= 150) OR tag="beta"
    // → m2 (alpha, t=200>=150) and m3 (beta). NOT m1 (alpha, t=100<150), NOT m4
    // (gamma).
    let req = filter_request(
        or_filter(vec![
            and_filter(vec![tag_filter("alpha"), created_ts_filter(ComparisonType::Gte, 150)]),
            tag_filter("beta"),
        ]),
        10,
    );
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob2"), eq("blob3")]);

    // NOT (tag="alpha" OR tag="beta") → m4 (gamma) only.
    let req =
        filter_request(not_filter(or_filter(vec![tag_filter("alpha"), tag_filter("beta")])), 10);
    assert_that!(search_blob_ids(&db, &req)?, unordered_elements_are![eq("blob4")]);

    Ok(())
}

// =============================================================================
// Search API v2: sort tests
// =============================================================================

#[gtest]
fn test_search_memories_v2_sort_created_timestamp_descending() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-sort-ts-desc-test"))?;

    for i in 0..5 {
        let mut m = mem_tagged(&format!("m{i}"), &["common"]);
        m.created_timestamp = ts(100 * (i as i64 + 1));
        db.add_memory(&m, format!("blob{i}"))?;
    }

    let req = sorted_request(
        tag_filter("common"),
        SortValue::CreatedTimestampSort(TimeSort { order: SortOrder::OrderDescending as i32 }),
    );
    // Latest first: blob4, blob3, blob2, blob1, blob0
    assert_that!(
        search_blob_ids(&db, &req)?,
        elements_are![eq("blob4"), eq("blob3"), eq("blob2"), eq("blob1"), eq("blob0")]
    );
    Ok(())
}

#[gtest]
fn test_search_memories_v2_sort_created_timestamp_ascending() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-sort-ts-asc-test"))?;

    for i in 0..5 {
        let mut m = mem_tagged(&format!("m{i}"), &["common"]);
        m.created_timestamp = ts(100 * (i as i64 + 1));
        db.add_memory(&m, format!("blob{i}"))?;
    }

    let req = sorted_request(
        tag_filter("common"),
        SortValue::CreatedTimestampSort(TimeSort { order: SortOrder::OrderAscending as i32 }),
    );
    // Oldest first: blob0, blob1, blob2, blob3, blob4
    assert_that!(
        search_blob_ids(&db, &req)?,
        elements_are![eq("blob0"), eq("blob1"), eq("blob2"), eq("blob3"), eq("blob4")]
    );
    Ok(())
}

#[gtest]
fn test_search_memories_v2_sort_event_timestamp_descending() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-sort-event-desc-test"))?;

    let mut m0 = mem_tagged("m0", &["common"]);
    m0.event_timestamp = ts(500);
    db.add_memory(&m0, "blob0".into())?;

    let mut m1 = mem_tagged("m1", &["common"]);
    m1.event_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    // m2: no event_timestamp — propertyWeights returns 0
    db.add_memory(&mem_tagged("m2", &["common"]), "blob2".into())?;

    let req = sorted_request(
        tag_filter("common"),
        SortValue::EventTimestampSort(TimeSort { order: SortOrder::OrderDescending as i32 }),
    );
    assert_that!(search_blob_ids(&db, &req)?, elements_are![eq("blob0"), eq("blob1"), eq("blob2")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_sort_event_timestamp_ascending() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-sort-event-asc-test"))?;

    let mut m0 = mem_tagged("m0", &["common"]);
    m0.event_timestamp = ts(500);
    db.add_memory(&m0, "blob0".into())?;

    let mut m1 = mem_tagged("m1", &["common"]);
    m1.event_timestamp = ts(100);
    db.add_memory(&m1, "blob1".into())?;

    // m2: no event_timestamp
    db.add_memory(&mem_tagged("m2", &["common"]), "blob2".into())?;

    // Ascending: m1 (100) < m0 (500), then m2 (missing) last.
    let req = sorted_request(
        tag_filter("common"),
        SortValue::EventTimestampSort(TimeSort { order: SortOrder::OrderAscending as i32 }),
    );
    assert_that!(search_blob_ids(&db, &req)?, elements_are![eq("blob1"), eq("blob0"), eq("blob2")]);
    Ok(())
}

#[gtest]
fn test_search_memories_v2_sort_expiration_timestamp_descending() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-sort-exp-desc-test"))?;

    let mut m0 = mem_tagged("m0", &["common"]);
    m0.expiration_timestamp = ts(1000);
    db.add_memory(&m0, "blob0".into())?;

    let mut m1 = mem_tagged("m1", &["common"]);
    m1.expiration_timestamp = ts(300);
    db.add_memory(&m1, "blob1".into())?;

    // m2: no expiration_timestamp
    db.add_memory(&mem_tagged("m2", &["common"]), "blob2".into())?;

    let req = sorted_request(
        tag_filter("common"),
        SortValue::ExpirationTimestampSort(TimeSort { order: SortOrder::OrderDescending as i32 }),
    );
    assert_that!(search_blob_ids(&db, &req)?, elements_are![eq("blob0"), eq("blob1"), eq("blob2")]);
    Ok(())
}

/// Verifies that documents with the same event_timestamp are returned in a
/// deterministic order (by creation timestamp, i.e. insertion order).
#[gtest]
fn test_search_memories_v2_sort_event_timestamp_tiebreaker() -> anyhow::Result<()> {
    let mut db = IcingMetaDatabase::new(IcingTempDir::new("v2-sort-tiebreak-test"))?;

    // Insert 5 memories all with the same event_timestamp.
    for i in 0..5 {
        let mut m = mem_tagged(&format!("m{i}"), &["common"]);
        m.event_timestamp = ts(1000);
        db.add_memory(&m, format!("blob{i}"))?;
    }

    // Descending: tiebreaker is creationTimestamp DESC → newer first.
    let req = sorted_request(
        tag_filter("common"),
        SortValue::EventTimestampSort(TimeSort { order: SortOrder::OrderDescending as i32 }),
    );
    let result = search_blob_ids(&db, &req)?;
    assert_that!(
        result,
        elements_are![eq("blob4"), eq("blob3"), eq("blob2"), eq("blob1"), eq("blob0")]
    );

    // Same query again → stable order.
    let result2 = search_blob_ids(&db, &req)?;
    assert_that!(result, eq(&result2));

    // Ascending: tiebreaker is creationTimestamp ASC → older first.
    let req_asc = sorted_request(
        tag_filter("common"),
        SortValue::EventTimestampSort(TimeSort { order: SortOrder::OrderAscending as i32 }),
    );
    let result_asc = search_blob_ids(&db, &req_asc)?;
    assert_that!(
        result_asc,
        elements_are![eq("blob0"), eq("blob1"), eq("blob2"), eq("blob3"), eq("blob4")]
    );
    Ok(())
}

#[gtest]
fn test_search_memories_v2_embedding_filter_with_type() -> anyhow::Result<()> {
    use sealed_memory_rust_proto::oak::private_memory::search_memories_filter::Value;
    let mut icing_database =
        IcingMetaDatabase::new(IcingTempDir::new("v2-embedding-filter-type-test"))?;

    let model_signature = "test_model".to_string();

    let memory1 = Memory {
        id: "m1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view1".to_string(),
                r#type: "wrong_type".to_string(),
                embedding: Some(Embedding {
                    model_signature: model_signature.clone(),
                    values: vec![1.0, 0.0, 0.0],
                }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "m2".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view2".to_string(),
                r#type: "correct_type".to_string(),
                embedding: Some(Embedding {
                    model_signature: model_signature.clone(),
                    values: vec![1.0, 0.0, 0.0],
                }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    let request = SearchMemoriesRequest {
        filter: Some(SearchMemoriesFilter {
            value: Some(Value::EmbeddingFilter(EmbeddingFilter {
                embedding: Some(Embedding {
                    model_signature: model_signature.clone(),
                    values: vec![0.9, 0.1, 0.1],
                }),
                minimum_score: 0.5,
                view_type: "correct_type".to_string(),
            })),
        }),
        page_size: 10,
        ..Default::default()
    };
    let (results, _) = icing_database.search_memories(&request)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();

    assert_that!(blob_ids, unordered_elements_are![eq("blob2")]);

    Ok(())
}

#[gtest]
fn test_search_memories_v2_embedding_filter() -> anyhow::Result<()> {
    let _ = env_logger::builder().filter(None, log::LevelFilter::Trace).try_init();

    use sealed_memory_rust_proto::oak::private_memory::search_memories_filter::Value;
    let mut icing_database = IcingMetaDatabase::new(IcingTempDir::new("v2-embedding-filter-test"))?;

    let model_signature = "test_model".to_string();

    let memory1 = Memory {
        id: "m1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view1".to_string(),
                embedding: Some(Embedding {
                    model_signature: model_signature.clone(),
                    values: vec![1.0, 0.0, 0.0],
                }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "m2".to_string(),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: "view2".to_string(),
                embedding: Some(Embedding {
                    model_signature: model_signature.clone(),
                    values: vec![0.0, 1.0, 0.0],
                }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    let request = SearchMemoriesRequest {
        filter: Some(SearchMemoriesFilter {
            value: Some(Value::EmbeddingFilter(EmbeddingFilter {
                embedding: Some(Embedding {
                    model_signature: model_signature.clone(),
                    values: vec![0.9, 0.1, 0.1],
                }),
                minimum_score: 0.5,
                view_type: "".to_string(),
            })),
        }),
        page_size: 10,
        ..Default::default()
    };
    let (results, _) = icing_database.search_memories(&request)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();

    assert_that!(blob_ids, unordered_elements_are![eq("blob1")]);

    Ok(())
}

#[gtest]
fn test_search_memories_v2_embedding_filter_multiple_view_types() -> anyhow::Result<()> {
    use sealed_memory_rust_proto::oak::private_memory::search_memories_filter::Value;
    let mut icing_database =
        IcingMetaDatabase::new(IcingTempDir::new("v2-embedding-filter-type-test"))?;

    let model_signature = "test_model".to_string();

    // This memory has two views, both of the wrong type, so should be filtered out.
    let memory1 = Memory {
        id: "m1".to_string(),
        views: Some(LlmViews {
            llm_views: vec![
                LlmView {
                    id: "view1".to_string(),
                    r#type: "wrong_type".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                },
                LlmView {
                    id: "view2".to_string(),
                    r#type: "wrong_type".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                },
            ],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    // This memory has two views, the first one is wrong, the second one is right.
    let memory2 = Memory {
        id: "m2".to_string(),
        views: Some(LlmViews {
            llm_views: vec![
                LlmView {
                    id: "view3".to_string(),
                    r#type: "wrong_type".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                },
                LlmView {
                    id: "view4".to_string(),
                    r#type: "correct_type".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                },
            ],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    // This memory has two views, the first one is right, the second one is wrong.
    let memory3 = Memory {
        id: "m3".to_string(),
        views: Some(LlmViews {
            llm_views: vec![
                LlmView {
                    id: "view5".to_string(),
                    r#type: "correct_type".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                },
                LlmView {
                    id: "view6".to_string(),
                    r#type: "wrong_type".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                },
            ],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory3, "blob3".to_string())?;

    // This memory has two views, the both right type, but only the second one
    // passes distance.
    let memory4 = Memory {
        id: "m4".to_string(),
        views: Some(LlmViews {
            llm_views: vec![
                LlmView {
                    id: "view7".to_string(),
                    r#type: "correct_type".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: vec![0.0, 0.0, 1.0],
                    }),
                    ..Default::default()
                },
                LlmView {
                    id: "view8".to_string(),
                    r#type: "correct_type".to_string(),
                    embedding: Some(Embedding {
                        model_signature: model_signature.clone(),
                        values: vec![1.0, 0.0, 0.0],
                    }),
                    ..Default::default()
                },
            ],
        }),
        ..Default::default()
    };
    icing_database.add_memory(&memory4, "blob4".to_string())?;

    let request = SearchMemoriesRequest {
        filter: Some(SearchMemoriesFilter {
            value: Some(Value::EmbeddingFilter(EmbeddingFilter {
                embedding: Some(Embedding {
                    model_signature: model_signature.clone(),
                    values: vec![0.9, 0.1, 0.1],
                }),
                minimum_score: 0.5,
                view_type: "correct_type".to_string(),
            })),
        }),
        page_size: 10,
        ..Default::default()
    };
    let (results, _) = icing_database.search_memories(&request)?;
    let blob_ids: Vec<String> = results.items.iter().map(|r| r.blob_id.clone()).collect();

    assert_that!(blob_ids, unordered_elements_are![eq("blob2"), eq("blob3"), eq("blob4")]);

    Ok(())
}
