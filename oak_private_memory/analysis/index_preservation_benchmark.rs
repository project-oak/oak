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

//! Index Preservation Benchmark
//!
//! Compares two cold-start initialization strategies:
//! 1. **Ground truth only** (current): Export schema + document log, rebuild
//!    index from scratch on initialize().
//! 2. **Full directory copy** (proposed): Copy the entire icing directory
//!    including pre-built index files, skip rebuild on initialize().
//!
//! Measures initialization latency and storage overhead for each approach.

use std::{fs, path::Path, time::Instant};

use anyhow::Result;
use clap::Parser;
use icing::IcingGroundTruthFilesHelper;
use oak_private_memory_database::icing::{IcingMetaDatabase, IcingTempDir};
use prost::Message;
use rand::random;
use sealed_memory_rust_proto::oak::private_memory::{Embedding, LlmView, LlmViews, Memory};

/// Index preservation benchmark: ground-truth rebuild vs full directory copy.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Size of the embedding vector
    #[arg(short, long, default_value_t = 768)]
    embedding_size: usize,

    /// Maximum number of embeddings to test (powers of 2 starting from 1000)
    #[arg(short, long, default_value_t = 64_000)]
    max_embeddings: u32,

    /// Number of iterations per data point
    #[arg(short = 'i', long, default_value_t = 5)]
    iterations: u32,

    /// Print verbose output
    #[arg(short = 'b', long)]
    verbose: bool,
}

/// Create a memory with a random embedding.
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

/// Recursively calculate directory size.
fn get_dir_size(path: &Path) -> Result<u64> {
    let mut total: u64 = 0;
    if path.is_file() {
        return Ok(fs::metadata(path)?.len());
    }
    if path.is_dir() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let p = entry.path();
            if p.is_file() {
                total += fs::metadata(&p)?.len();
            } else if p.is_dir() {
                total += get_dir_size(&p)?;
            }
        }
    }
    Ok(total)
}

/// Recursively copy a directory.
fn copy_dir_all(src: &Path, dst: &Path) -> Result<()> {
    fs::create_dir_all(dst)?;
    for entry in fs::read_dir(src)? {
        let entry = entry?;
        let src_path = entry.path();
        let dst_path = dst.join(entry.file_name());
        if src_path.is_dir() {
            copy_dir_all(&src_path, &dst_path)?;
        } else {
            fs::copy(&src_path, &dst_path)?;
        }
    }
    Ok(())
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

/// Ground truth file paths.
const GROUND_TRUTH_PATHS: &[&str] = &[
    "schema_dir/schema.pb",
    "schema_dir/overlay_schema.pb",
    "schema_dir/schema_store_header",
    "document_dir/document_log_v1",
];

/// Measure ground truth size vs total size.
fn measure_sizes(base_dir: &str) -> Result<(u64, u64)> {
    let base = Path::new(base_dir);
    let mut gt_size: u64 = 0;
    for rel in GROUND_TRUTH_PATHS {
        let p = base.join(rel);
        if p.exists() {
            gt_size += fs::metadata(&p)?.len();
        }
    }
    let total = get_dir_size(base)?;
    Ok((gt_size, total))
}

struct TimingStats {
    _min_ms: f64,
    avg_ms: f64,
    _max_ms: f64,
    avg_icing_ms: f64,
}

/// Strategy A: ground truth only (current approach).
/// Exports ground truth, migrates to new dir, initializes (rebuilds index).
fn measure_ground_truth_init(db: &IcingMetaDatabase, iterations: u32) -> Result<TimingStats> {
    use icing::{create_icing_search_engine, get_default_icing_options};

    let ground_truth = db.export()?;

    let mut ext_ms = Vec::with_capacity(iterations as usize);
    let mut icing_ms = Vec::with_capacity(iterations as usize);

    for _ in 0..iterations {
        let rebuild_dir = IcingTempDir::new("icing-gt-rebuild-");
        ground_truth.migrate(rebuild_dir.as_str())?;

        let start = Instant::now();
        let options = get_default_icing_options(rebuild_dir.as_str()).encode_to_vec();
        let engine = create_icing_search_engine(&options);
        let result = engine.initialize()?;
        let elapsed = start.elapsed().as_secs_f64() * 1000.0;

        ext_ms.push(elapsed);
        icing_ms.push(result.initialize_stats.and_then(|s| s.latency_ms).unwrap_or(0) as f64);
    }

    Ok(TimingStats {
        _min_ms: ext_ms.iter().cloned().fold(f64::INFINITY, f64::min),
        avg_ms: ext_ms.iter().sum::<f64>() / iterations as f64,
        _max_ms: ext_ms.iter().cloned().fold(0.0, f64::max),
        avg_icing_ms: icing_ms.iter().sum::<f64>() / iterations as f64,
    })
}

/// Strategy B: full directory copy (proposed approach).
/// Copies entire icing directory (including index), initializes (no rebuild).
fn measure_full_copy_init(source_dir: &str, iterations: u32) -> Result<TimingStats> {
    use icing::{create_icing_search_engine, get_default_icing_options};

    let src = Path::new(source_dir);

    let mut ext_ms = Vec::with_capacity(iterations as usize);
    let mut icing_ms = Vec::with_capacity(iterations as usize);

    for _ in 0..iterations {
        let copy_dir = IcingTempDir::new("icing-fullcopy-");

        // Copy the full directory (ground truth + index files)
        let copy_start = Instant::now();
        copy_dir_all(src, Path::new(copy_dir.as_str()))?;
        let copy_elapsed = copy_start.elapsed().as_secs_f64() * 1000.0;

        // Initialize (should skip index rebuild since index files exist)
        let init_start = Instant::now();
        let options = get_default_icing_options(copy_dir.as_str()).encode_to_vec();
        let engine = create_icing_search_engine(&options);
        let _result = engine.initialize()?;
        let init_elapsed = init_start.elapsed().as_secs_f64() * 1000.0;

        // Total = copy + init
        ext_ms.push(copy_elapsed + init_elapsed);
        icing_ms.push(init_elapsed);
    }

    Ok(TimingStats {
        _min_ms: ext_ms.iter().cloned().fold(f64::INFINITY, f64::min),
        avg_ms: ext_ms.iter().sum::<f64>() / iterations as f64,
        _max_ms: ext_ms.iter().cloned().fold(0.0, f64::max),
        avg_icing_ms: icing_ms.iter().sum::<f64>() / iterations as f64,
    })
}

/// Generate embedding counts (1k, 2k, 4k, ...).
fn get_embedding_counts(max: u32) -> Vec<u32> {
    let mut counts = Vec::new();
    let mut c = 1000;
    while c <= max {
        counts.push(c);
        c *= 2;
    }
    counts
}

fn main() -> Result<()> {
    let args = Args::parse();
    icing::set_logging(false);

    println!("Index Preservation Benchmark");
    println!("============================\n");
    println!(
        "Configuration: embedding_size={}, iterations={}\n",
        args.embedding_size, args.iterations
    );

    let counts = get_embedding_counts(args.max_embeddings);

    // Print header
    println!(
        "| {:>10} | {:>12} | {:>12} | {:>14} | {:>14} | {:>14} | {:>14} | {:>10} |",
        "Embeddings",
        "GT Size",
        "Total Size",
        "GT Rebuild(ms)",
        "FullCopy(ms)",
        "Init Only(ms)",
        "Savings(ms)",
        "Speedup"
    );
    println!(
        "|------------|--------------|--------------|----------------|----------------|----------------|----------------|------------|"
    );

    for &count in &counts {
        let temp_dir = IcingTempDir::new("icing-idx-bench-");
        let dir_path = temp_dir.as_str().to_string();

        let mut db = IcingMetaDatabase::new(temp_dir)?;

        if args.verbose {
            eprintln!("populating {} embeddings...", count);
        }

        for i in 0..count {
            let memory = create_memory_with_embedding(i, args.embedding_size);
            db.add_memory(&memory, format!("blob_{}", i))?;
        }

        db.optimize()?;

        // Measure sizes
        let (gt_size, total_size) = measure_sizes(&dir_path)?;

        if args.verbose {
            eprintln!("measuring ground truth rebuild...");
        }
        let gt_stats = measure_ground_truth_init(&db, args.iterations)?;

        if args.verbose {
            eprintln!("measuring full directory copy...");
        }
        let fc_stats = measure_full_copy_init(&dir_path, args.iterations)?;

        let savings = gt_stats.avg_ms - fc_stats.avg_ms;
        let speedup = gt_stats.avg_ms / fc_stats.avg_ms;

        println!(
            "| {:>10} | {:>12} | {:>12} | {:>14.1} | {:>14.1} | {:>14.1} | {:>14.1} | {:>9.1}x |",
            count,
            format_bytes(gt_size),
            format_bytes(total_size),
            gt_stats.avg_ms,
            fc_stats.avg_ms,
            fc_stats.avg_icing_ms,
            savings,
            speedup,
        );

        drop(db);
    }

    Ok(())
}
