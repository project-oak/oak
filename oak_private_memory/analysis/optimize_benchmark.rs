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

//! Icing.Optimize latency benchmark
//!
//! Measures the cost of calling optimize() on a ~30MB database filled with
//! embeddings. The benchmark:
//! 1. Fills the database to ~30MB with embedding memories
//! 2. Calls optimize
//! 3. Adds one memory, calls optimize (repeat N times)
//! 4. Reports latency for each optimize call

use std::time::Instant;

use anyhow::Result;
use oak_private_memory_database::icing::{IcingDatabaseConfig, IcingMetaDatabase, IcingTempDir};
use prost::Message;
use rand::random;
use sealed_memory_rust_proto::oak::private_memory::{Embedding, LlmView, LlmViews, Memory};

const EMBEDDING_SIZE: usize = 768;
const TARGET_DB_SIZE_MB: usize = 30;
const INCREMENTAL_ROUNDS: usize = 20;

fn create_memory_with_embedding(index: usize) -> Memory {
    let values: Vec<f32> = (0..EMBEDDING_SIZE).map(|_| random::<f32>()).collect();
    Memory {
        id: format!("memory_{index}"),
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

fn get_db_size(db: &IcingMetaDatabase) -> Result<usize> {
    let exported_data = db.export()?.encode_to_vec();
    Ok(exported_data.len())
}

fn main() -> Result<()> {
    let config = IcingDatabaseConfig {
        base_dir: IcingTempDir::new("optimize-bench-"),
        enable_int8_embedding: false,
    };
    let mut db = IcingMetaDatabase::new(config)?;

    // Phase 1: fill to ~30MB
    println!("=== Phase 1: filling database to ~{TARGET_DB_SIZE_MB}MB ===");
    let target_bytes = TARGET_DB_SIZE_MB * 1024 * 1024;
    let mut index: usize = 0;
    loop {
        let memory = create_memory_with_embedding(index);
        db.add_memory(&memory, format!("blob_{index}"))?;
        index += 1;

        if index.is_multiple_of(500) {
            let size = get_db_size(&db)?;
            println!("  {index} memories, export size: {:.2} MB", size as f64 / (1024.0 * 1024.0));
            if size >= target_bytes {
                break;
            }
        }
    }

    let size = get_db_size(&db)?;
    println!("filled {index} memories, export size: {:.2} MB", size as f64 / (1024.0 * 1024.0));

    // Phase 2: initial optimize on the full DB
    println!("\n=== Phase 2: initial optimize on full database ===");
    let start = Instant::now();
    db.optimize()?;
    let elapsed = start.elapsed();
    println!("  optimize took: {:.1}ms", elapsed.as_secs_f64() * 1000.0);

    // Phase 3: add 1 memory + optimize, repeated
    println!("\n=== Phase 3: add 1 memory + optimize (x{INCREMENTAL_ROUNDS}) ===");
    println!("{:<8} {:>15} {:>15}", "round", "add_ms", "optimize_ms");
    println!("{}", "-".repeat(42));

    for round in 0..INCREMENTAL_ROUNDS {
        let memory = create_memory_with_embedding(index);

        let add_start = Instant::now();
        db.add_memory(&memory, format!("blob_{index}"))?;
        let add_elapsed = add_start.elapsed();

        let opt_start = Instant::now();
        db.optimize()?;
        let opt_elapsed = opt_start.elapsed();

        println!(
            "{:<8} {:>14.1}  {:>14.1}",
            round + 1,
            add_elapsed.as_secs_f64() * 1000.0,
            opt_elapsed.as_secs_f64() * 1000.0,
        );

        index += 1;
    }

    let final_size = get_db_size(&db)?;
    println!(
        "\nfinal: {} memories, export size: {:.2} MB",
        index,
        final_size as f64 / (1024.0 * 1024.0)
    );

    // Phase 4: back-to-back optimize with NO changes
    println!("\n=== Phase 4: optimize with NO changes (x5) ===");
    for round in 1..=5 {
        let opt_start = Instant::now();
        db.optimize()?;
        let opt_elapsed = opt_start.elapsed();
        println!("  round {round}: {:.1}ms", opt_elapsed.as_secs_f64() * 1000.0);
    }

    // Phase 5: GetOptimizeInfo latency comparison
    println!("\n=== Phase 5: GetOptimizeInfo latency ===");

    // 5a: GetOptimizeInfo with no pending changes (just optimized)
    println!("\n--- after optimize (no pending changes) ---");
    for round in 1..=5 {
        let start = Instant::now();
        let info = db.get_optimize_info()?;
        let elapsed = start.elapsed();
        println!(
            "  round {round}: {:.3}ms (optimizable_docs={}, est_bytes={}, time_since_last={}ms)",
            elapsed.as_secs_f64() * 1000.0,
            info.optimizable_docs(),
            info.estimated_optimizable_bytes(),
            info.time_since_last_optimize_ms(),
        );
    }

    // 5b: Add some memories, then check GetOptimizeInfo
    println!("\n--- after adding 100 memories (without optimize) ---");
    for i in 0..100 {
        let memory = create_memory_with_embedding(index + i);
        db.add_memory(&memory, format!("blob_{}", index + i))?;
    }
    index += 100;

    for round in 1..=5 {
        let start = Instant::now();
        let info = db.get_optimize_info()?;
        let elapsed = start.elapsed();
        println!(
            "  round {round}: {:.3}ms (optimizable_docs={}, est_bytes={}, time_since_last={}ms)",
            elapsed.as_secs_f64() * 1000.0,
            info.optimizable_docs(),
            info.estimated_optimizable_bytes(),
            info.time_since_last_optimize_ms(),
        );
    }

    // 5c: Delete some memories, then check GetOptimizeInfo
    println!("\n--- after deleting 50 memories ---");
    for i in 0..50 {
        let _ = db.delete_memories(&[format!("memory_{i}")]);
    }

    for round in 1..=5 {
        let start = Instant::now();
        let info = db.get_optimize_info()?;
        let elapsed = start.elapsed();
        println!(
            "  round {round}: {:.3}ms (optimizable_docs={}, est_bytes={}, time_since_last={}ms)",
            elapsed.as_secs_f64() * 1000.0,
            info.optimizable_docs(),
            info.estimated_optimizable_bytes(),
            info.time_since_last_optimize_ms(),
        );
    }

    let final_size2 = get_db_size(&db)?;
    println!(
        "\nfinal: {} memories, export size: {:.2} MB",
        index,
        final_size2 as f64 / (1024.0 * 1024.0)
    );

    Ok(())
}
