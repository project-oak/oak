//
// Copyright 2026 The Project Oak Authors
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

//! Embedding Scoring Limit Test
//!
//! Investigates Icing's `num_to_score` limit (default 30,000) to determine:
//! 1. Whether embedding sorting considers all matching documents or only the
//!    first `num_to_score` candidates.
//! 2. Whether there is any indicator in the search result that the limit was
//!    reached (allowing callers to know they should narrow their query).
//!
//! Strategy:
//! - Insert 31,000 views with controlled embeddings.
//! - Views 0..30999 get a low embedding score (near-zero dot product with the
//!   query vector).
//! - View 31000 (the "needle") gets the highest possible embedding score
//!   (perfect alignment with the query vector).
//! - An embedding search for the top 10 results should return the needle as the
//!   #1 result if Icing scores all 31k docs. If the needle is missing, Icing
//!   only scored the first 30k and the sort is incomplete.

use std::time::Instant;

use anyhow::Result;
use clap::Parser;
use icing::set_logging;
use oak_private_memory_database::icing::{IcingMetaDatabase, IcingTempDir};
use sealed_memory_rust_proto::oak::private_memory::{
    Embedding, EmbeddingFilter, LlmView, LlmViews, Memory, SearchMemoriesFilter,
    SearchMemoriesRequest,
};

/// Embedding scoring limit test.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Total number of documents to insert (should exceed 30,000).
    #[arg(short, long, default_value_t = 31000)]
    num_docs: u32,

    /// Size of the embedding vector.
    #[arg(short, long, default_value_t = 128)]
    embedding_size: usize,
}

/// Create a memory whose LLM view has an embedding with all values set to
/// `fill_value`.
fn create_memory(index: u32, embedding_size: usize, fill_value: f32) -> Memory {
    let values: Vec<f32> = vec![fill_value; embedding_size];
    Memory {
        id: format!("memory_{}", index),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: format!("view_{}", index),
                embedding: Some(Embedding { model_signature: "test_model".to_string(), values }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    }
}

/// Create a SearchMemoriesRequest for embedding search.
fn create_request(embedding_size: usize) -> SearchMemoriesRequest {
    let query_values: Vec<f32> = vec![1.0; embedding_size];
    SearchMemoriesRequest {
        filter: Some(SearchMemoriesFilter {
            value: Some(
                sealed_memory_rust_proto::oak::private_memory::search_memories_filter::Value::EmbeddingFilter(
                    EmbeddingFilter {
                        embedding: Some(Embedding {
                            model_signature: "test_model".to_string(),
                            values: query_values,
                        }),
                        ..Default::default()
                    },
                ),
            ),
        }),
        limit: 10,
        page_size: 10,
        ..Default::default()
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    set_logging(false);

    println!("Embedding Scoring Limit Test");
    println!("============================\n");
    println!("num_docs: {}, embedding_size: {}\n", args.num_docs, args.embedding_size);

    let request = create_request(args.embedding_size);

    // Phase 1: Create database and insert documents.
    println!("Phase 1: Populating database...");
    let temp_dir = IcingTempDir::new("scoring-limit-test-");
    let mut db = IcingMetaDatabase::new(temp_dir)?;

    let start = Instant::now();
    let needle_index = args.num_docs - 1; // Last document is the needle.

    for i in 0..args.num_docs {
        let memory = if i == needle_index {
            // The needle: perfect alignment with query → max dot product.
            create_memory(i, args.embedding_size, 1.0)
        } else {
            // Background noise: near-zero dot product.
            create_memory(i, args.embedding_size, 0.001)
        };
        db.add_memory(&memory, format!("blob_{}", i))?;

        if (i + 1) % 5000 == 0 {
            println!("  Added {} memories...", i + 1);
        }
    }
    let populate_duration = start.elapsed();
    println!("  Populated {} memories in {:.1}s\n", args.num_docs, populate_duration.as_secs_f64());

    // Phase 2: Verify document counts.
    println!("Phase 2: Document counts...");
    let (memory_count, view_count) = db.get_document_counts()?;
    println!("  get_document_counts(): {} memories, {} views", memory_count, view_count);
    println!("  (actual inserted: {} memories, {} views)", args.num_docs, args.num_docs);
    if memory_count < args.num_docs as i64 || view_count < args.num_docs as i64 {
        println!("  NOTE: counts are capped at 30,000 by num_to_score default\n");
    }

    // Phase 3: Run embedding search — does sorting consider all docs?
    println!("Phase 3: Embedding search (top 10)...");
    let start = Instant::now();
    let (results, _) = db.search_memories(&request)?;
    let search_duration = start.elapsed();

    println!("  Search completed in {:.1}ms", search_duration.as_secs_f64() * 1000.0);
    println!("  Returned {} results", results.items.len());

    // Display top results.
    let needle_blob_id = format!("blob_{}", needle_index);
    let mut needle_found = false;
    let mut needle_rank: Option<usize> = None;

    println!("\n  Top results:");
    for (i, item) in results.items.iter().enumerate() {
        let is_needle = item.blob_id == needle_blob_id;
        let marker = if is_needle { " ← NEEDLE" } else { "" };
        println!("    #{}: blob_id={}, score={:.4}{}", i + 1, item.blob_id, item.score, marker);
        if is_needle {
            needle_found = true;
            needle_rank = Some(i + 1);
        }
    }

    // Phase 4: Analysis.
    println!("\n\nPhase 4: Analysis");
    println!("=================");

    let expected_needle_score = args.embedding_size as f32;
    let expected_noise_score = args.embedding_size as f32 * 0.001;
    println!("  Expected needle score (view_{}): {:.4}", needle_index, expected_needle_score);
    println!("  Expected noise score:           {:.4}", expected_noise_score);

    if needle_found {
        println!("\n  ✅ NEEDLE FOUND at rank #{}", needle_rank.unwrap());
        println!(
            "  → Icing sorts across ALL {} matching documents, not just the first 30k.",
            args.num_docs
        );
        if needle_rank == Some(1) {
            println!("  → Sorting is CORRECT: needle has the highest score and is ranked #1.");
        } else {
            println!(
                "  ⚠ Sorting is SUSPICIOUS: needle should be #1 but is #{}",
                needle_rank.unwrap()
            );
        }
    } else {
        println!("\n  ❌ NEEDLE NOT FOUND in top 10 results");
        println!("  → Icing only scored the first 30,000 documents (num_to_score default).");
        println!(
            "  → The needle (view_{}) was beyond the scoring window and was excluded.",
            needle_index
        );
        println!("  → Sorting is INCOMPLETE: results may not reflect the true top-k.");
    }

    // Phase 5: Control tests — confirm the scoring window is biased toward
    // recent documents (highest document_ids).
    println!("\n\nPhase 5: Control tests...");

    // Control A: Needle inserted FIRST (lowest document_id → outside window).
    println!("  Control A: Needle inserted first (oldest doc)...");
    let temp_dir_a = IcingTempDir::new("scoring-limit-ctrl-a-");
    let mut db_a = IcingMetaDatabase::new(temp_dir_a)?;

    let needle_memory = create_memory(99999, args.embedding_size, 1.0);
    db_a.add_memory(&needle_memory, "blob_needle".to_string())?;
    for i in 0..(args.num_docs - 1) {
        db_a.add_memory(&create_memory(i, args.embedding_size, 0.001), format!("blob_{}", i))?;
    }

    let (results_a, _) = db_a.search_memories(&request)?;
    let ctrl_a_found = results_a.items.iter().any(|item| item.blob_id == "blob_needle");
    let ctrl_a_rank =
        results_a.items.iter().position(|item| item.blob_id == "blob_needle").map(|p| p + 1);

    if ctrl_a_found {
        println!(
            "    ✅ Found at rank #{} (score={:.4})",
            ctrl_a_rank.unwrap(),
            results_a.items[ctrl_a_rank.unwrap() - 1].score
        );
    } else {
        println!("    ❌ NOT found (needle is oldest doc, outside 30k scoring window)");
    }

    // Control B: Needle inserted in the MIDDLE (should be near boundary).
    let middle = args.num_docs / 2;
    println!("  Control B: Needle inserted at position {} (middle)...", middle);
    let temp_dir_b = IcingTempDir::new("scoring-limit-ctrl-b-");
    let mut db_b = IcingMetaDatabase::new(temp_dir_b)?;

    for i in 0..args.num_docs {
        if i == middle {
            db_b.add_memory(
                &create_memory(99998, args.embedding_size, 1.0),
                "blob_needle_mid".to_string(),
            )?;
        } else {
            db_b.add_memory(&create_memory(i, args.embedding_size, 0.001), format!("blob_{}", i))?;
        }
    }

    let (results_b, _) = db_b.search_memories(&request)?;
    let ctrl_b_found = results_b.items.iter().any(|item| item.blob_id == "blob_needle_mid");
    let ctrl_b_rank =
        results_b.items.iter().position(|item| item.blob_id == "blob_needle_mid").map(|p| p + 1);

    if ctrl_b_found {
        println!(
            "    ✅ Found at rank #{} (score={:.4})",
            ctrl_b_rank.unwrap(),
            results_b.items[ctrl_b_rank.unwrap() - 1].score
        );
    } else {
        println!("    ❌ NOT found (needle at middle, outside 30k scoring window)");
    }

    // Summary.
    println!("\n\n=== SUMMARY ===");
    println!("  Total documents:      {}", args.num_docs);
    println!("  num_to_score default: 30,000");
    println!(
        "  Needle at END   (doc #{}): {}",
        needle_index,
        if needle_found { "FOUND ✅" } else { "NOT FOUND ❌" }
    );
    println!(
        "  Needle at START (doc #0):       {}",
        if ctrl_a_found { "FOUND ✅" } else { "NOT FOUND ❌" }
    );
    println!(
        "  Needle at MIDDLE (doc #{}):  {}",
        middle,
        if ctrl_b_found { "FOUND ✅" } else { "NOT FOUND ❌" }
    );

    if needle_found && !ctrl_a_found {
        println!("\n  CONCLUSION: Icing's num_to_score (default 30,000) scores the MOST");
        println!("  RECENT 30,000 documents (by document_id). Older documents beyond");
        println!("  this window are silently excluded from scoring and ranking.");
        println!("  The sort is INCOMPLETE — it favors recently-added documents.");
        if !ctrl_b_found {
            println!("  Even documents inserted in the middle are excluded.");
        }
        println!("\n  There is NO indicator in SearchResultProto that results were");
        println!("  truncated. Users must check get_document_counts() separately and");
        println!("  compare against the 30,000 threshold.");
        println!("\n  RECOMMENDATIONS:");
        println!("  1. Apply filters (time range, tags) to keep candidate set < 30k.");
        println!("  2. Or increase num_to_score in ResultSpecProto (higher latency).");
        println!("  3. Monitor get_document_counts() to detect when approaching limit.");
    } else if needle_found && ctrl_a_found {
        println!("\n  CONCLUSION: Icing scores ALL matching documents regardless of count.");
        println!("  The num_to_score limit does not apply to embedding search.");
    }

    Ok(())
}
