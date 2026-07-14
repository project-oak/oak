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

//! Batch Delete Benchmark
//!
//! Measures how fast `IcingMetaDatabase::delete_memories` is and, crucially,
//! how its cost scales with the size of the database. Two experiments are run:
//!
//! * Experiment A ("delete all"): seed `N` memories, then delete all `N` in a
//!   single `delete_memories` call. Reports total latency, per-memory latency
//!   and the scaling ratio between successive sizes. If the per-memory column
//!   stays flat the operation is linear; if it climbs, the operation is
//!   super-linear.
//!
//! * Experiment B ("fixed batch on a growing corpus"): seed `N` memories, then
//!   delete a *fixed* number `K` of them. This isolates the per-delete cost as
//!   a function of the resident corpus size `N`. If deleting a fixed `K` grows
//!   with `N`, then each individual delete is O(N) (the tell-tale sign of the
//!   whole-corpus index scan hypothesised for the delete lookup query).
//!
//! Every memory is seeded with one small-embedding LLM view and a far-future
//! expiration timestamp, mirroring the load-test setup where all documents are
//! non-expired.

use std::time::Instant;

use anyhow::Result;
use clap::Parser;
use oak_private_memory_database::{
    IcingMetaDatabase, IcingTempDir, icing::IcingDatabaseConfig, system_time_to_timestamp,
};
use rand::random;
use sealed_memory_rust_proto::oak::private_memory::{Embedding, LlmView, LlmViews, Memory};

/// Batch delete benchmark for the Icing-backed metadata database.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Comma-separated corpus sizes to test.
    #[arg(long, default_value = "100,200,400,800,1600")]
    sizes: String,

    /// Number of repetitions per size (a fresh database is built each time).
    #[arg(long, default_value_t = 3)]
    repetitions: u32,

    /// Fixed number of memories to delete in Experiment B.
    #[arg(long, default_value_t = 50)]
    fixed_batch: usize,

    /// Embedding vector size for the seeded view.
    #[arg(long, default_value_t = 8)]
    embedding_size: usize,
}

/// Create a memory with a single small-embedding view and a far-future
/// expiration timestamp (so it is always "non-expired").
fn make_memory(index: usize, embedding_size: usize) -> Memory {
    let values: Vec<f32> = (0..embedding_size).map(|_| random::<f32>()).collect();
    // ~10 years in the future, matching a load test where nothing has expired.
    let expiration =
        std::time::SystemTime::now() + std::time::Duration::from_secs(10 * 365 * 24 * 3600);
    Memory {
        id: format!("memory_{index}"),
        expiration_timestamp: Some(system_time_to_timestamp(expiration)),
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: format!("view_{index}"),
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

/// Build a fresh database seeded with `n` memories, compacted with `optimize`
/// so the starting state is clean (no pre-existing soft-deleted documents).
fn seed_db(n: usize, embedding_size: usize) -> Result<IcingMetaDatabase> {
    let temp_dir = IcingTempDir::new("icing-delete-benchmark-");
    let mut db = IcingMetaDatabase::new(IcingDatabaseConfig {
        base_dir: temp_dir,
        enable_int8_embedding: false,
    })?;
    for i in 0..n {
        db.add_memory(&make_memory(i, embedding_size), format!("blob_{i}"))?;
    }
    db.optimize()?;
    Ok(db)
}

/// Simple summary statistics over a set of millisecond samples.
struct Stats {
    mean_ms: f64,
    min_ms: f64,
    max_ms: f64,
}

fn summarize(samples: &[f64]) -> Stats {
    let mean_ms = samples.iter().sum::<f64>() / samples.len() as f64;
    let min_ms = samples.iter().cloned().fold(f64::INFINITY, f64::min);
    let max_ms = samples.iter().cloned().fold(0.0, f64::max);
    Stats { mean_ms, min_ms, max_ms }
}

/// Experiment A: seed `n`, delete all `n` in one call.
fn bench_delete_all(sizes: &[usize], repetitions: u32, embedding_size: usize) -> Result<()> {
    println!("\n=== Experiment A: delete ALL N in a single batch call ===");
    println!(
        "| {:>6} | {:>10} | {:>10} | {:>10} | {:>14} | {:>13} | {:>10} |",
        "N", "mean (ms)", "min (ms)", "max (ms)", "per-mem (us)", "ratio vs prev", "mem/sec"
    );
    println!(
        "|--------|------------|------------|------------|----------------|---------------|------------|"
    );

    let mut prev_mean: Option<f64> = None;
    for &n in sizes {
        let mut samples = Vec::with_capacity(repetitions as usize);
        for _ in 0..repetitions {
            let mut db = seed_db(n, embedding_size)?;
            let ids: Vec<String> = (0..n).map(|i| format!("memory_{i}")).collect();
            let start = Instant::now();
            let not_found = db.delete_memories(&ids)?;
            let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;
            assert!(not_found.is_empty(), "unexpected not-found ids: {}", not_found.len());
            samples.push(elapsed_ms);
            drop(db);
        }
        let stats = summarize(&samples);
        let per_mem_us = stats.mean_ms * 1000.0 / n as f64;
        let ratio = prev_mean.map(|p| stats.mean_ms / p);
        let mem_per_sec = n as f64 / (stats.mean_ms / 1000.0);
        println!(
            "| {:>6} | {:>10.2} | {:>10.2} | {:>10.2} | {:>14.2} | {:>13} | {:>10.0} |",
            n,
            stats.mean_ms,
            stats.min_ms,
            stats.max_ms,
            per_mem_us,
            ratio.map(|r| format!("{r:.2}x")).unwrap_or_else(|| "-".to_string()),
            mem_per_sec,
        );
        prev_mean = Some(stats.mean_ms);
    }
    Ok(())
}

/// Experiment B: seed `n`, delete a fixed `k`. Isolates per-delete cost as a
/// function of resident corpus size.
fn bench_fixed_batch(
    sizes: &[usize],
    repetitions: u32,
    fixed_batch: usize,
    embedding_size: usize,
) -> Result<()> {
    println!(
        "\n=== Experiment B: delete a FIXED {fixed_batch} memories from a corpus of size N ==="
    );
    println!(
        "| {:>6} | {:>12} | {:>12} | {:>16} | {:>13} |",
        "N", "mean (ms)", "min (ms)", "per-delete (us)", "ratio vs prev"
    );
    println!("|--------|--------------|--------------|------------------|---------------|");

    let mut prev_mean: Option<f64> = None;
    for &n in sizes {
        if fixed_batch > n {
            continue;
        }
        let mut samples = Vec::with_capacity(repetitions as usize);
        for _ in 0..repetitions {
            let mut db = seed_db(n, embedding_size)?;
            // Delete the first `fixed_batch` memories.
            let ids: Vec<String> = (0..fixed_batch).map(|i| format!("memory_{i}")).collect();
            let start = Instant::now();
            let not_found = db.delete_memories(&ids)?;
            let elapsed_ms = start.elapsed().as_secs_f64() * 1000.0;
            assert!(not_found.is_empty(), "unexpected not-found ids: {}", not_found.len());
            samples.push(elapsed_ms);
            drop(db);
        }
        let stats = summarize(&samples);
        let per_delete_us = stats.mean_ms * 1000.0 / fixed_batch as f64;
        let ratio = prev_mean.map(|p| stats.mean_ms / p);
        println!(
            "| {:>6} | {:>12.3} | {:>12.3} | {:>16.2} | {:>13} |",
            n,
            stats.mean_ms,
            stats.min_ms,
            per_delete_us,
            ratio.map(|r| format!("{r:.2}x")).unwrap_or_else(|| "-".to_string()),
        );
        prev_mean = Some(stats.mean_ms);
    }
    Ok(())
}

fn main() -> Result<()> {
    let args = Args::parse();
    let sizes: Vec<usize> =
        args.sizes.split(',').map(|s| s.trim().parse::<usize>()).collect::<Result<_, _>>()?;

    println!("Batch Delete Benchmark");
    println!("======================");
    println!(
        "sizes={:?}, repetitions={}, fixed_batch={}, embedding_size={}",
        sizes, args.repetitions, args.fixed_batch, args.embedding_size
    );

    bench_delete_all(&sizes, args.repetitions, args.embedding_size)?;
    bench_fixed_batch(&sizes, args.repetitions, args.fixed_batch, args.embedding_size)?;

    Ok(())
}
