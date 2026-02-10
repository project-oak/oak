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
//! 3. Index rebuild time from ground truth files (initialization latency)

use std::{fs, path::Path, time::Instant};

use anyhow::Result;
use clap::Parser;
use icing::{IcingGroundTruthFilesHelper, set_logging};
use oak_private_memory_database::icing::{IcingMetaDatabase, IcingTempDir};
use prost::Message;
use rand::random;
use sealed_memory_rust_proto::oak::private_memory::{Embedding, LlmView, LlmViews, Memory};

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

    /// Number of iterations for index rebuild benchmarking
    #[arg(short = 'i', long, default_value_t = 5)]
    rebuild_iterations: u32,

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

/// Statistics for index rebuild timing.
struct RebuildStats {
    /// Minimum external timing (wall clock)
    min_external_ms: f64,
    /// Maximum external timing (wall clock)
    max_external_ms: f64,
    /// Average external timing (wall clock)
    avg_external_ms: f64,
    /// Average internal Icing latency (from InitializeStatsProto.latency_ms)
    avg_icing_internal_ms: f64,
}

/// Measure index rebuild time by running multiple iterations.
/// This exports ground truth, then rebuilds the index from scratch multiple
/// times. Reports both external (wall clock) and internal (Icing's
/// InitializeStatsProto.latency_ms) timing.
fn measure_rebuild_time(db: &IcingMetaDatabase, iterations: u32) -> Result<RebuildStats> {
    use icing::{create_icing_search_engine, get_default_icing_options};

    // Export ground truth files
    let ground_truth = db.export()?;

    let mut external_durations_ms = Vec::with_capacity(iterations as usize);
    let mut internal_durations_ms = Vec::with_capacity(iterations as usize);

    for _ in 0..iterations {
        // Create a fresh temp directory for rebuild
        let rebuild_dir = IcingTempDir::new("icing-rebuild-");

        // Migrate ground truth files to the new directory
        ground_truth.migrate(rebuild_dir.as_str())?;

        // Measure external wall clock time
        let start = Instant::now();

        // Use low-level API to get InitializeResultProto with stats
        let options_bytes = get_default_icing_options(rebuild_dir.as_str()).encode_to_vec();
        let icing_search_engine = create_icing_search_engine(&options_bytes);
        let init_result = icing_search_engine.initialize()?;

        let external_elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;
        external_durations_ms.push(external_elapsed_ms);

        // Extract internal timing from InitializeStatsProto
        let internal_latency_ms =
            init_result.initialize_stats.and_then(|stats| stats.latency_ms).unwrap_or(0) as f64;
        internal_durations_ms.push(internal_latency_ms);

        // rebuild_dir is dropped here, cleaning up
    }

    let total_external_ms: f64 = external_durations_ms.iter().sum();
    let min_external_ms = external_durations_ms.iter().cloned().fold(f64::INFINITY, f64::min);
    let max_external_ms = external_durations_ms.iter().cloned().fold(0.0, f64::max);
    let avg_external_ms = total_external_ms / iterations as f64;

    let total_internal_ms: f64 = internal_durations_ms.iter().sum();
    let avg_icing_internal_ms = total_internal_ms / iterations as f64;

    Ok(RebuildStats { min_external_ms, max_external_ms, avg_external_ms, avg_icing_internal_ms })
}

fn main() -> Result<()> {
    let args = Args::parse();

    // Disable icing verbose logging for cleaner output
    set_logging(false);

    println!("Icing Database Benchmark");
    println!("========================\n");
    println!(
        "Configuration: embedding_size={}, queries_per_test={}, rebuild_iterations={}\n",
        args.embedding_size, args.queries, args.rebuild_iterations
    );

    let embedding_counts = get_embedding_counts(args.max_embeddings);

    // Print combined table header for storage and rebuild time (external vs
    // internal)
    println!(
        "| {:>12} | {:>15} | {:>15} | {:>15} | {:>14} | {:>14} | {:>14} | {:>14} |",
        "Embeddings",
        "Ground Truth",
        "Index Files",
        "Total Size",
        "Ext Min (ms)",
        "Ext Avg (ms)",
        "Ext Max (ms)",
        "Icing Avg (ms)"
    );
    println!(
        "|--------------|-----------------|-----------------|-----------------|----------------|----------------|----------------|----------------|"
    );

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

        // Measure directory sizes
        let (ground_truth_size, index_size) = measure_directory_sizes(&dir_path)?;
        let total_size = ground_truth_size + index_size;

        // Measure index rebuild time
        if args.verbose {
            println!("Measuring index rebuild time ({} iterations)...", args.rebuild_iterations);
        }
        let rebuild_stats = measure_rebuild_time(&db, args.rebuild_iterations)?;

        println!(
            "| {:>12} | {:>15} | {:>15} | {:>15} | {:>14.1} | {:>14.1} | {:>14.1} | {:>14.1} |",
            target_count,
            format_bytes(ground_truth_size),
            format_bytes(index_size),
            format_bytes(total_size),
            rebuild_stats.min_external_ms,
            rebuild_stats.avg_external_ms,
            rebuild_stats.max_external_ms,
            rebuild_stats.avg_icing_internal_ms,
        );

        // Database and temp_dir are dropped here, cleaning up the directory
        drop(db);
    }

    Ok(())
}
