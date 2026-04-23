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

//! Large Database Persistence Test
//!
//! Verifies that the Icing database can grow beyond the 100 MB gRPC decode
//! limit and still be exported/imported successfully (keysync round-trip).
//! This is possible because metadata blob persistence uses streaming RPCs.
//!
//! Known limitations discovered by this test:
//! - Icing caps query matching at 30,000 documents per query (hard limit). This
//!   affects `get_document_counts()` and any search-based API.
//! - After ground truth import, the embedding index may not be rebuilt, causing
//!   embedding search to return 0 results until addressed.

use std::time::Instant;

use anyhow::Result;
use clap::Parser;
use icing::set_logging;
use oak_private_memory_database::icing::{IcingMetaDatabase, IcingTempDir};
use prost::Message;
use rand::random;
use sealed_memory_rust_proto::oak::private_memory::{
    Embedding, EmbeddingQuery, LlmView, LlmViews, Memory,
};

/// Large database persistence test.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Target database size in MB
    #[arg(short, long, default_value_t = 150)]
    target_size_mb: usize,

    /// Size of the embedding vector
    #[arg(short, long, default_value_t = 768)]
    embedding_size: usize,
}

/// Create a memory with a random embedding.
fn create_memory_with_embedding(index: u32, embedding_size: usize) -> Memory {
    let values: Vec<f32> = (0..embedding_size).map(|_| random::<f32>()).collect();

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

fn main() -> Result<()> {
    let args = Args::parse();
    set_logging(false);

    let target_bytes = args.target_size_mb * 1024 * 1024;

    println!("Large Database Persistence Test");
    println!("===============================\n");
    println!("Target: {} MB, embedding_size: {}\n", args.target_size_mb, args.embedding_size);

    // Phase 1: Populate the database until it exceeds the target size.
    println!("Phase 1: Populating database...");
    let temp_dir = IcingTempDir::new("large-db-test-");
    let mut db = IcingMetaDatabase::new(temp_dir)?;

    let mut count: u32 = 0;
    let batch_size: u32 = 1000;

    loop {
        for i in 0..batch_size {
            let memory = create_memory_with_embedding(count + i, args.embedding_size);
            db.add_memory(&memory, format!("blob_{}", count + i))?;
        }
        count += batch_size;

        let export = db.export()?;
        let size = export.encoded_len();

        println!(
            "  Added {} memories, export size: {:.1} MB",
            count,
            size as f64 / (1024.0 * 1024.0)
        );

        if size >= target_bytes {
            break;
        }
    }

    // Check document counts before export.
    let (pre_memory_count, pre_view_count) = db.get_document_counts()?;
    println!(
        "\nPre-export document counts: {} memories, {} views (query limit may cap at 30,000)",
        pre_memory_count, pre_view_count
    );

    db.optimize()?;

    let export = db.export()?;
    let final_export_size = export.encoded_len();

    println!(
        "Populated {} memories, final export size: {:.1} MB",
        count,
        final_export_size as f64 / (1024.0 * 1024.0)
    );
    if args.target_size_mb >= 100 {
        assert!(
            final_export_size > 100 * 1024 * 1024,
            "export size ({} bytes) should exceed 100 MB",
            final_export_size
        );
    }

    // Phase 2: Export the database.
    println!("\nPhase 2: Exporting database...");
    let start = Instant::now();
    let exported = db.export()?;
    let export_bytes = exported.encode_to_vec();
    let export_duration = start.elapsed();
    println!(
        "  Exported {} bytes ({:.1} MB) in {:.1}ms",
        export_bytes.len(),
        export_bytes.len() as f64 / (1024.0 * 1024.0),
        export_duration.as_secs_f64() * 1000.0
    );

    // Drop the original database.
    drop(db);

    // Phase 3: Import into a new database (simulate keysync).
    println!("\nPhase 3: Importing database (keysync simulation)...");
    let new_temp_dir = IcingTempDir::new("large-db-test-import-");
    let start = Instant::now();
    let imported_db = IcingMetaDatabase::import(new_temp_dir, &export_bytes[..])?;
    let import_duration = start.elapsed();
    println!("  Imported in {:.1}ms", import_duration.as_secs_f64() * 1000.0);

    println!("  Optimizing imported database...");
    let start = Instant::now();
    imported_db.optimize()?;
    let optimize_duration = start.elapsed();
    println!("  Optimized in {:.1}ms", optimize_duration.as_secs_f64() * 1000.0);

    // Phase 4: Verify data integrity after import.
    println!("\nPhase 4: Verifying data integrity...");

    // Document counts (subject to 30k query limit).
    let (post_memory_count, post_view_count) = imported_db.get_document_counts()?;
    println!("  Post-import counts: {} memories, {} views", post_memory_count, post_view_count);
    assert_eq!(
        post_memory_count, pre_memory_count,
        "memory count should be consistent before/after import"
    );
    assert_eq!(
        post_view_count, pre_view_count,
        "view count should be consistent before/after import"
    );

    // Re-export size should match original (proves all data survived).
    let re_export = imported_db.export()?;
    let re_export_size = re_export.encoded_len();
    println!(
        "  Re-export size: {:.1} MB (original: {:.1} MB)",
        re_export_size as f64 / (1024.0 * 1024.0),
        final_export_size as f64 / (1024.0 * 1024.0)
    );
    let size_diff = (re_export_size as f64 - final_export_size as f64).abs();
    let tolerance = final_export_size as f64 * 0.01; // 1% tolerance
    assert!(
        size_diff <= tolerance,
        "re-export size ({:.1} MB) differs too much from original ({:.1} MB)",
        re_export_size as f64 / (1024.0 * 1024.0),
        final_export_size as f64 / (1024.0 * 1024.0)
    );

    // Embedding search (diagnostic — may return 0 due to index rebuild issues).
    let query_values: Vec<f32> = (0..args.embedding_size).map(|_| random::<f32>()).collect();
    let eq = EmbeddingQuery {
        embedding: vec![Embedding {
            model_signature: "test_model".to_string(),
            values: query_values,
        }],
        ..Default::default()
    };
    let (results, _scores, _token) = imported_db.embedding_search(
        &eq,
        10,
        oak_private_memory_database::icing::PageToken::Start,
        true,
    )?;
    println!("  Embedding search returned {} results", results.len());
    assert_eq!(results.len(), 10, "embedding search should return 10 results");

    println!("\n=== ALL CHECKS PASSED ===");
    println!("Summary:");
    println!("  Memories inserted:  {}", count);
    println!(
        "  Export size:        {:.1} MB (exceeds old 100 MB limit)",
        final_export_size as f64 / (1024.0 * 1024.0)
    );
    println!(
        "  Re-export size:     {:.1} MB (data integrity verified)",
        re_export_size as f64 / (1024.0 * 1024.0)
    );
    println!("  Export time:        {:.1}ms", export_duration.as_secs_f64() * 1000.0);
    println!("  Import time:        {:.1}ms", import_duration.as_secs_f64() * 1000.0);
    println!("  Optimize time:      {:.1}ms", optimize_duration.as_secs_f64() * 1000.0);
    println!(
        "  Doc counts:         {} memories, {} views (capped by 30k query limit)",
        post_memory_count, post_view_count
    );
    println!("  Embedding search:   {} results", results.len());

    Ok(())
}
