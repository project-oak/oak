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

//! Icing Database Benchmark
//!
//! This benchmark measures:
//! 1. Embedding search latency at various scales (1k to 1M embeddings)
//! 2. Icing directory size breakdown (ground truth vs indexing files)

use std::{
    fs,
    path::Path,
    time::{Duration, Instant},
};

use anyhow::Result;
use clap::Parser;
use icing::set_logging;
use oak_private_memory_database::icing::{IcingMetaDatabase, IcingTempDir, PageToken};
use rand::random;
use sealed_memory_rust_proto::oak::private_memory::{
    Embedding, EmbeddingQuery, LlmView, LlmViews, Memory,
};

/// Icing database benchmark for embedding search latency and directory size.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Number of queries to run for latency measurement
    #[arg(short, long, default_value_t = 10)]
    queries: u32,

    /// Size of the embedding vector
    #[arg(short, long, default_value_t = 3072)]
    embedding_size: usize,

    /// Maximum number of embeddings to test (will test powers of 2 up to this)
    #[arg(short, long, default_value_t = 1_048_576)]
    max_embeddings: u32,

    /// Print verbose output
    #[arg(short = 'b', long)]
    verbose: bool,
}

/// Ground truth file paths in the icing directory.
const GROUND_TRUTH_PATHS: &[&str] = &[
    "schema_dir/schema.pb",
    "schema_dir/overlay_schema.pb",
    "schema_dir/schema_store_header",
    "document_dir/document_log_v1",
];

/// Create a memory with a random embedding of the specified size.
fn create_memory_with_embedding(index: u32, embedding_size: usize) -> Memory {
    let values: Vec<f32> = (0..embedding_size).map(|_| random::<f32>()).collect();

    Memory {
        id: format!("memory_{}", index),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: format!("view_{}", index),
                embedding: Some(Embedding {
                    model_signature: "benchmark_model".to_string(),
                    values,
                }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    }
}

/// Create a random query embedding of the specified size.
fn create_embedding_query(embedding_size: usize) -> EmbeddingQuery {
    let values: Vec<f32> = (0..embedding_size).map(|_| random::<f32>()).collect();

    EmbeddingQuery {
        embedding: vec![Embedding { model_signature: "benchmark_model".to_string(), values }],
        ..Default::default()
    }
}

/// Measure search latency by running multiple queries.
fn measure_search_latency(
    db: &IcingMetaDatabase,
    embedding_size: usize,
    num_queries: u32,
) -> Duration {
    let mut total_duration = Duration::ZERO;

    for _ in 0..num_queries {
        let query = create_embedding_query(embedding_size);
        let start = Instant::now();
        // Use embedding_search directly with larger page_size for accurate measurements
        let _ = db.embedding_search(&query, 100, PageToken::Start, true);
        total_duration += start.elapsed();
    }

    total_duration / num_queries
}

/// Calculate the size of a directory recursively.
fn get_dir_size(path: &Path) -> Result<u64> {
    let mut total_size: u64 = 0;

    if path.is_file() {
        return Ok(fs::metadata(path)?.len());
    }

    if path.is_dir() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let entry_path = entry.path();
            if entry_path.is_file() {
                total_size += fs::metadata(&entry_path)?.len();
            } else if entry_path.is_dir() {
                total_size += get_dir_size(&entry_path)?;
            }
        }
    }

    Ok(total_size)
}

/// Measure directory sizes, separating ground truth from index files.
fn measure_directory_sizes(base_dir: &str) -> Result<(u64, u64)> {
    let base_path = Path::new(base_dir);

    // Calculate ground truth size
    let mut ground_truth_size: u64 = 0;
    for rel_path in GROUND_TRUTH_PATHS {
        let full_path = base_path.join(rel_path);
        if full_path.exists() {
            ground_truth_size += fs::metadata(&full_path)?.len();
        }
    }

    // Calculate total size
    let total_size = get_dir_size(base_path)?;

    // Index size is total minus ground truth
    let index_size = total_size.saturating_sub(ground_truth_size);

    Ok((ground_truth_size, index_size))
}

/// Format bytes as human-readable size.
fn format_bytes(bytes: u64) -> String {
    const KB: u64 = 1024;
    const MB: u64 = KB * 1024;
    const GB: u64 = MB * 1024;

    if bytes >= GB {
        format!("{:.2} GB", bytes as f64 / GB as f64)
    } else if bytes >= MB {
        format!("{:.2} MB", bytes as f64 / MB as f64)
    } else if bytes >= KB {
        format!("{:.2} KB", bytes as f64 / KB as f64)
    } else {
        format!("{} B", bytes)
    }
}

/// Generate embedding counts to test (1k, 2k, 4k, ..., up to max).
fn get_embedding_counts(max_embeddings: u32) -> Vec<u32> {
    let mut counts = Vec::new();
    let mut count = 1000;
    while count <= max_embeddings {
        counts.push(count);
        count *= 2;
    }
    counts
}

fn main() -> Result<()> {
    let args = Args::parse();

    // Disable icing verbose logging for cleaner output
    set_logging(false);

    println!("Icing Database Benchmark");
    println!("========================\n");
    println!(
        "Configuration: embedding_size={}, queries_per_test={}\n",
        args.embedding_size, args.queries
    );

    let embedding_counts = get_embedding_counts(args.max_embeddings);

    // Print combined table header for latency and storage
    println!(
        "| {:>12} | {:>18} | {:>15} | {:>15} | {:>15} |",
        "Embeddings", "Avg Latency (ms)", "Ground Truth", "Index Files", "Total Size"
    );
    println!("|--------------|----------------------|-----------------|-----------------|-----------------|");

    for &target_count in &embedding_counts {
        // Create a temp directory and store its path before passing ownership
        let temp_dir = IcingTempDir::new("icing-benchmark-");
        let dir_path = temp_dir.as_str().to_string();

        // Create a fresh database for each test
        let mut db = IcingMetaDatabase::new(temp_dir)?;

        if args.verbose {
            println!("Populating database with {} embeddings...", target_count);
        }

        // Add embeddings
        for i in 0..target_count {
            let memory = create_memory_with_embedding(i, args.embedding_size);
            db.add_memory(&memory, format!("blob_{}", i))?;
        }

        // Optimize before measuring
        db.optimize()?;

        // Measure search latency
        let avg_latency = measure_search_latency(&db, args.embedding_size, args.queries);
        let latency_ms = avg_latency.as_secs_f64() * 1000.0;

        // Measure directory sizes
        let (ground_truth_size, index_size) = measure_directory_sizes(&dir_path)?;
        let total_size = ground_truth_size + index_size;

        println!(
            "| {:>12} | {:>18.3} | {:>15} | {:>15} | {:>15} |",
            target_count,
            latency_ms,
            format_bytes(ground_truth_size),
            format_bytes(index_size),
            format_bytes(total_size)
        );

        // Database and temp_dir are dropped here, cleaning up the directory
        drop(db);
    }

    Ok(())
}
