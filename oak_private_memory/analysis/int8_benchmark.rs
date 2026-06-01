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

//! Int8 Embedding Benchmark
//!
//! Compares float32 vs int8 quantized embeddings using controlled recall tests:
//!
//! 1. **Corpus**: N memories with L2-normalized random embeddings.
//! 2. **Queries**: Each query is constructed by choosing K known "ground truth"
//!    nearest neighbors from the corpus, then forming a query vector as their
//!    weighted average plus small Gaussian noise (re-normalized). This
//!    guarantees the true nearest neighbors are known.
//! 3. **Metrics**: For each mode (float32, int8) we measure:
//!    - Insert + optimize time
//!    - Export size (serialized ground truth)
//!    - Search latency (avg / min / max)
//!    - Recall@K against known ground truth neighbors

use std::time::Instant;

use anyhow::Result;
use clap::Parser;
use oak_private_memory_database::icing::{IcingDatabaseConfig, IcingMetaDatabase, IcingTempDir};
use prost::Message;
use rand::random;
use sealed_memory_rust_proto::oak::private_memory::{
    Embedding, EmbeddingSort, LlmView, LlmViews, Memory, SearchMemoriesRequest, SearchMemoriesSort,
    search_memories_sort,
};

/// Int8 vs float32 embedding benchmark with planted nearest neighbors.
#[derive(Parser, Debug)]
#[command(author, version, about)]
struct Args {
    /// Number of memories to insert.
    #[arg(short, long, default_value_t = 1000)]
    memories: u32,

    /// Size of the embedding vector.
    #[arg(short, long, default_value_t = 768)]
    embedding_size: usize,

    /// Number of search queries to run.
    #[arg(short, long, default_value_t = 50)]
    queries: u32,

    /// Top-k results to request.
    #[arg(short, long, default_value_t = 10)]
    top_k: i32,

    /// Noise scale for query perturbation (smaller = query is closer to the
    /// ground truth neighbor, making the test easier).
    #[arg(long, default_value_t = 0.05)]
    noise_scale: f64,
}

/// Generate a random L2-normalized vector.
fn random_unit_vector(dim: usize) -> Vec<f32> {
    let v: Vec<f32> = (0..dim).map(|_| random::<f32>() * 2.0 - 1.0).collect();
    normalize(&v)
}

/// L2-normalize a vector. Returns zero vector if norm is zero.
fn normalize(v: &[f32]) -> Vec<f32> {
    let norm: f32 = v.iter().map(|x| x * x).sum::<f32>().sqrt();
    if norm < 1e-10 {
        return vec![0.0; v.len()];
    }
    v.iter().map(|x| x / norm).collect()
}

/// Compute dot product between two vectors.
fn dot(a: &[f32], b: &[f32]) -> f64 {
    a.iter().zip(b.iter()).map(|(x, y)| *x as f64 * *y as f64).sum()
}

/// Create a query that is a noisy version of a weighted average of the given
/// ground-truth embeddings. The resulting vector is re-normalized.
fn create_query_near(neighbors: &[&Vec<f32>], noise_scale: f64, dim: usize) -> Vec<f32> {
    // Start with the average of the neighbor embeddings.
    let mut query = vec![0.0f64; dim];
    for emb in neighbors {
        for (i, val) in emb.iter().enumerate() {
            query[i] += *val as f64;
        }
    }
    let n = neighbors.len() as f64;
    for x in query.iter_mut() {
        *x /= n;
    }

    // Add Gaussian-like noise (using Box-Muller from uniform random).
    for x in query.iter_mut() {
        let u1: f64 = random::<f64>().max(1e-10);
        let u2: f64 = random::<f64>();
        let noise = (-2.0 * u1.ln()).sqrt() * (2.0 * std::f64::consts::PI * u2).cos();
        *x += noise_scale * noise;
    }

    let query_f32: Vec<f32> = query.iter().map(|x| *x as f32).collect();
    normalize(&query_f32)
}

fn create_memory(id: &str, values: &[f32]) -> Memory {
    Memory {
        id: id.to_string(),
        tags: vec!["benchmark".into()],
        views: Some(LlmViews {
            llm_views: vec![LlmView {
                id: format!("view_{}", id),
                embedding: Some(Embedding {
                    model_signature: "benchmark_model".to_string(),
                    values: values.to_vec(),
                }),
                ..Default::default()
            }],
        }),
        ..Default::default()
    }
}

fn create_search_request(query_embedding: &[f32], top_k: i32) -> SearchMemoriesRequest {
    let embedding = Embedding {
        model_signature: "benchmark_model".to_string(),
        values: query_embedding.to_vec(),
    };
    SearchMemoriesRequest {
        // Sort by embedding similarity (dot product, descending).
        sort: vec![SearchMemoriesSort {
            sort: Some(search_memories_sort::Sort::EmbeddingSort(EmbeddingSort {
                embedding: Some(embedding.clone()),
                ..Default::default()
            })),
        }],
        limit: top_k,
        page_size: top_k,
        ..Default::default()
    }
}

struct BenchmarkResult {
    label: String,
    insert_ms: f64,
    export_size_bytes: usize,
    avg_search_ms: f64,
    min_search_ms: f64,
    max_search_ms: f64,
    /// Fraction of ground-truth top-k that appeared in the returned top-k.
    avg_recall: f64,
}

/// Compute the "true" top-k neighbors by brute-force dot product.
fn brute_force_top_k(query: &[f32], corpus: &[Vec<f32>], k: usize) -> Vec<usize> {
    let mut scores: Vec<(usize, f64)> =
        corpus.iter().enumerate().map(|(i, emb)| (i, dot(query, emb))).collect();
    scores.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());
    scores.iter().take(k).map(|(i, _)| *i).collect()
}

fn run_benchmark(
    label: &str,
    config: IcingDatabaseConfig,
    corpus: &[Vec<f32>],
    queries: &[(Vec<f32>, Vec<usize>)], // (query_vec, ground_truth_indices)
    top_k: i32,
) -> Result<BenchmarkResult> {
    // Insert
    let insert_start = Instant::now();
    let mut db = IcingMetaDatabase::new(config)?;
    for (i, emb) in corpus.iter().enumerate() {
        let memory = create_memory(&format!("mem_{}", i), emb);
        db.add_memory(&memory, format!("blob_{}", i))?;
    }
    db.optimize()?;
    let insert_elapsed = insert_start.elapsed();

    // Export size
    let export_size = db.export()?.encoded_len();

    // Search + recall
    let mut search_times = Vec::new();
    let mut recalls = Vec::new();

    for (query_vec, ground_truth) in queries {
        let request = create_search_request(query_vec, top_k);
        let start = Instant::now();
        let (results, _) = db.search_memories(&request)?;
        let elapsed = start.elapsed();
        search_times.push(elapsed.as_secs_f64() * 1000.0);

        // Compute recall: how many of the ground truth IDs are in the results?
        let returned_ids: Vec<String> =
            results.items.iter().map(|item| item.blob_id.clone()).collect();
        let ground_truth_ids: Vec<String> =
            ground_truth.iter().map(|i| format!("blob_{}", i)).collect();

        let hits = ground_truth_ids.iter().filter(|gt| returned_ids.contains(gt)).count();
        let recall = hits as f64 / ground_truth_ids.len().max(1) as f64;
        recalls.push(recall);
    }

    let avg_search_ms = search_times.iter().sum::<f64>() / search_times.len() as f64;
    let min_search_ms = search_times.iter().cloned().fold(f64::INFINITY, f64::min);
    let max_search_ms = search_times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);
    let avg_recall = recalls.iter().sum::<f64>() / recalls.len() as f64;

    Ok(BenchmarkResult {
        label: label.to_string(),
        insert_ms: insert_elapsed.as_secs_f64() * 1000.0,
        export_size_bytes: export_size,
        avg_search_ms,
        min_search_ms,
        max_search_ms,
        avg_recall,
    })
}

fn main() -> Result<()> {
    let args = Args::parse();
    let top_k = args.top_k as usize;

    println!("=== Int8 vs Float32 Embedding Benchmark ===");
    println!(
        "Memories: {}, Dim: {}, Queries: {}, Top-k: {}, Noise: {}",
        args.memories, args.embedding_size, args.queries, args.top_k, args.noise_scale
    );
    println!();

    // Step 1: Generate normalized corpus.
    println!("Generating {} normalized {}-dim embeddings...", args.memories, args.embedding_size);
    let corpus: Vec<Vec<f32>> =
        (0..args.memories).map(|_| random_unit_vector(args.embedding_size)).collect();

    // Step 2: Generate queries with planted nearest neighbors.
    println!("Generating {} queries with planted nearest neighbors...", args.queries);
    let mut queries: Vec<(Vec<f32>, Vec<usize>)> = Vec::new();

    for _ in 0..args.queries {
        // Pick `top_k` random corpus indices as "ground truth" neighbors.
        // We pick the first one and construct a query close to it.
        let primary_idx = random::<u32>() as usize % corpus.len();

        // Create query near the primary neighbor.
        let query =
            create_query_near(&[&corpus[primary_idx]], args.noise_scale, args.embedding_size);

        // Compute true top-k by brute force.
        let ground_truth = brute_force_top_k(&query, &corpus, top_k);
        queries.push((query, ground_truth));
    }

    // Step 3: Run benchmarks.
    println!("\nRunning float32 benchmark...");
    let float32_result = run_benchmark(
        "float32",
        IcingDatabaseConfig {
            base_dir: IcingTempDir::new("int8-bench-"),
            enable_int8_embedding: false,
        },
        &corpus,
        &queries,
        args.top_k,
    )?;

    println!("Running int8 benchmark...");
    let int8_result = run_benchmark(
        "int8",
        IcingDatabaseConfig {
            base_dir: IcingTempDir::new("int8-bench-"),
            enable_int8_embedding: true,
        },
        &corpus,
        &queries,
        args.top_k,
    )?;

    // Step 4: Print results.
    println!();
    println!("=== Results ===");
    println!(
        "{:<10} {:>12} {:>14} {:>10} {:>10} {:>10} {:>10}",
        "Mode", "Insert (ms)", "Export (bytes)", "Avg (ms)", "Min (ms)", "Max (ms)", "Recall@K"
    );
    println!("{:-<86}", "");
    for r in [&float32_result, &int8_result] {
        println!(
            "{:<10} {:>12.1} {:>14} {:>10.3} {:>10.3} {:>10.3} {:>9.1}%",
            r.label,
            r.insert_ms,
            r.export_size_bytes,
            r.avg_search_ms,
            r.min_search_ms,
            r.max_search_ms,
            r.avg_recall * 100.0
        );
    }

    // Deltas.
    let size_pct = (1.0
        - int8_result.export_size_bytes as f64 / float32_result.export_size_bytes as f64)
        * 100.0;
    let latency_pct = (int8_result.avg_search_ms / float32_result.avg_search_ms - 1.0) * 100.0;

    println!();
    println!("--- Summary ---");
    println!("Export size reduction:    {:.1}%", size_pct);
    println!("Search latency change:   {:+.1}%", latency_pct);
    println!(
        "Recall@{}: float32={:.1}%, int8={:.1}%",
        args.top_k,
        float32_result.avg_recall * 100.0,
        int8_result.avg_recall * 100.0
    );

    Ok(())
}
