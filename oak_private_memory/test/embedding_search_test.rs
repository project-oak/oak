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

use anyhow::Context;
use googletest::prelude::*;
use oak_private_memory_database::{icing::IcingMetaDatabase, PageToken};
use sealed_memory_rust_proto::{
    oak::private_memory::{search_memory_query, EmbeddingQuery, SearchMemoryQuery},
    prelude::v1::*,
};
use tempfile::tempdir;

#[gtest]
fn test_embedding_search_returns_scores() -> anyhow::Result<()> {
    let temp_dir = tempdir()?;
    let mut icing_database =
        IcingMetaDatabase::new(temp_dir.path().to_str().context("invalid temp path")?)?;

    // Add memories with different embeddings
    let memory1 = Memory {
        id: "memory1".to_string(),
        embeddings: vec![Embedding {
            identifier: "test_model".to_string(),
            values: vec![1.0, 2.0, 3.0],
        }],
        ..Default::default()
    };
    icing_database.add_memory(&memory1, "blob1".to_string())?;

    let memory2 = Memory {
        id: "memory2".to_string(),
        embeddings: vec![Embedding {
            identifier: "test_model".to_string(),
            values: vec![4.0, 5.0, 6.0],
        }],
        ..Default::default()
    };
    icing_database.add_memory(&memory2, "blob2".to_string())?;

    // Query for memories with an embedding that is closer to memory2
    let embedding_query = SearchMemoryQuery {
        clause: Some(search_memory_query::Clause::EmbeddingQuery(EmbeddingQuery {
            embedding: vec![Embedding {
                identifier: "test_model".to_string(),
                values: vec![1.0, 1.0, 1.0],
            }],
            ..Default::default()
        })),
    };

    let (blob_ids, scores, _) = icing_database.search(&embedding_query, 10, PageToken::Start)?;
    assert_that!(scores, not(is_empty()));
    assert_that!(scores.len(), eq(blob_ids.len()));
    assert_that!(scores, each(predicate(|&x| x > 0.0)));
    assert_that!(scores[0], eq(15.0));
    assert_that!(scores[1], eq(6.0));
    Ok(())
}
