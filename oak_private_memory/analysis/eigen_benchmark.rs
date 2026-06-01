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

//! Eigen Embedding Search Benchmark
//!
//! Measures embedding search latency with Eigen enabled (the current build).
//! Compare results against the prior benchmark data collected without Eigen
//! to quantify the improvement from SIMD-optimized vector operations.
//!
//! The benchmark populates an Icing database with N embeddings and runs
//! embedding search queries, timing each search operation.

use std::time::Instant;

use anyhow::Result;
use clap::Parser;
use icing::set_logging;
use oak_private_memory_database::icing::{IcingDatabaseConfig, IcingMetaDatabase, IcingTempDir};
use rand::random;
use sealed_memory_rust_proto::oak::private_memory::{
    Embedding, EmbeddingFilter, EmbeddingSort, LlmView, LlmViews, Memory, SearchMemoriesFilter,
    SearchMemoriesRequest, SearchMemoriesSort, SortOrder,
};

/// Eigen embedding search benchmark.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Size of the embedding vector
    #[arg(short, long, default_value_t = 768)]
    embedding_size: usize,

    /// Maximum number of embeddings to test (powers of 2 starting from 1000)
    #[arg(short, long, default_value_t = 64_000)]
    max_embeddings: u32,

    /// Number of search iterations per data point
    #[arg(short = 'i', long, default_value_t = 20)]
    iterations: u32,
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

/// Create a SearchMemoriesRequest for embedding search.
fn create_request(embedding_size: usize) -> SearchMemoriesRequest {
    let values: Vec<f32> = (0..embedding_size).map(|_| random::<f32>()).collect();
    SearchMemoriesRequest {
        filter: Some(SearchMemoriesFilter {
            value: Some(
                sealed_memory_rust_proto::oak::private_memory::search_memories_filter::Value::EmbeddingFilter(
                    EmbeddingFilter {
                        embedding: Some(Embedding {
                            model_signature: "benchmark_model".to_string(),
                            values,
                        }),
                        ..Default::default()
                    },
                ),
            ),
        }),
        sort: vec![SearchMemoriesSort {
            sort: Some(
                sealed_memory_rust_proto::oak::private_memory::search_memories_sort::Sort::EmbeddingSort(
                    EmbeddingSort {
                        order: SortOrder::OrderDescending.into(),
                        embedding: Some(Embedding {
                            model_signature: "benchmark_model".to_string(),
                            values: (0..embedding_size).map(|_| random::<f32>()).collect(),
                        }),
                        ..Default::default()
                    },
                ),
            ),
        }],
        limit: 10,
        page_size: 10,
        ..Default::default()
    }
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

/// Measure embedding search latency over multiple iterations.
fn measure_search_latency(
    db: &IcingMetaDatabase,
    request: &SearchMemoriesRequest,
    iterations: u32,
) -> Result<(f64, f64, f64)> {
    let mut times = Vec::with_capacity(iterations as usize);

    for _ in 0..iterations {
        let start = Instant::now();
        let _results = db.search_memories(request)?;
        let elapsed = start.elapsed().as_secs_f64() * 1000.0;
        times.push(elapsed);
    }

    let min = times.iter().cloned().fold(f64::INFINITY, f64::min);
    let avg = times.iter().sum::<f64>() / iterations as f64;
    let max = times.iter().cloned().fold(0.0, f64::max);

    Ok((min, avg, max))
}

fn main() -> Result<()> {
    let args = Args::parse();
    set_logging(false);

    println!("Eigen Embedding Search Benchmark");
    println!("================================\n");
    println!(
        "Configuration: embedding_size={}, iterations={}\n",
        args.embedding_size, args.iterations
    );

    let counts = get_embedding_counts(args.max_embeddings);

    // Print header
    println!(
        "| {:>10} | {:>12} | {:>12} | {:>12} |",
        "Embeddings", "Min (ms)", "Avg (ms)", "Max (ms)"
    );
    println!("|------------|--------------|--------------|--------------| ");

    for &count in &counts {
        let temp_dir = IcingTempDir::new("icing-eigen-bench-");
        let mut db = IcingMetaDatabase::new(IcingDatabaseConfig {
            base_dir: temp_dir,
            enable_int8_embedding: false,
        })?;

        // Populate
        for i in 0..count {
            let memory = create_memory_with_embedding(i, args.embedding_size);
            db.add_memory(&memory, format!("blob_{}", i))?;
        }
        db.optimize()?;

        // Create request
        let request = create_request(args.embedding_size);

        // Warmup
        let _ = db.search_memories(&request)?;

        // Measure
        let (min, avg, max) = measure_search_latency(&db, &request, args.iterations)?;

        println!("| {:>10} | {:>12.2} | {:>12.2} | {:>12.2} |", count, min, avg, max);

        drop(db);
    }

    Ok(())
}
