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

use anyhow::Result;
use clap::Parser;
use oak_private_memory_database::{IcingMetaDatabase, IcingTempDir};
use prost::Message;
use rand::random;
use sealed_memory_rust_proto::oak::private_memory::{Embedding, LlmView, LlmViews, Memory};

/// A tool for analyzing the size of the icing database.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Number of memories to add
    #[arg(short, long, default_value_t = 10)]
    memories: u32,

    /// Number of tags per memory
    #[arg(short, long, default_value_t = 5)]
    tags: u32,

    /// Number of LLM views per memory
    #[arg(short, long, default_value_t = 2)]
    views: u32,

    /// Size of the embedding vector

    #[arg(short, long, default_value_t = 3072)]
    embedding_size: usize,

    /// The size limit of the database in megabytes (MB).
    #[arg(short, long)]
    database_size_limit: Option<u32>,

    /// Print details log.
    #[arg(short = 'b', long)]
    verbose: bool,
}

fn get_db_size(db: &IcingMetaDatabase) -> Result<usize> {
    let exported_data = db.export()?.encode_to_vec();

    Ok(exported_data.len())
}

fn create_memory(index: u32, args: &Args) -> Memory {
    let tags = (0..args.tags).map(|j| format!("tag_{}_{}", index, j)).collect();

    let llm_views = (0..args.views)
        .map(|j| {
            let values = (0..args.embedding_size).map(|_| random::<f32>()).collect();

            LlmView {
                id: format!("view_{}_{}", index, j),
                embedding: Some(Embedding { model_signature: "test_model".to_string(), values }),
                ..Default::default()
            }
        })
        .collect();

    Memory {
        id: random::<u64>().to_string(),
        tags,
        views: Some(LlmViews { llm_views }),
        ..Default::default()
    }
}

fn print_limit_analysis(limit_mb: u32, initial_size: usize, average_size_per_memory: usize) {
    let limit_bytes = limit_mb as usize * 1024 * 1024;
    if limit_bytes > initial_size {
        let available_size = limit_bytes - initial_size;
        let supported_memories =
            if average_size_per_memory > 0 { available_size / average_size_per_memory } else { 0 };
        println!(
            "With a {}MB limit, the database can support approximately {} memories.",
            limit_mb, supported_memories
        );
    } else {
        println!("The {}MB limit is smaller than the initial database size.", limit_mb);
    }
}

fn print_summary(
    args: &Args,
    initial_size: usize,
    final_size: usize,
    total_size_change: usize,
    average_size_per_memory: usize,
) {
    println!("\nSummary:");

    println!("Total memories added: {}", args.memories);
    println!(
        "Each memory: {} tags, {} views, embedding size {}",
        args.tags, args.views, args.embedding_size
    );

    println!("Final database size: {} bytes", final_size);

    println!("Total size increase: {} bytes", total_size_change);

    println!("Average size per memory: {} bytes", average_size_per_memory);

    if let Some(limit_mb) = args.database_size_limit {
        print_limit_analysis(limit_mb, initial_size, average_size_per_memory);
    }
}

fn print_optimization_details(before_size: usize, after_size: usize) {
    println!("\nAfter optimization:");
    println!("Optimized database size: {} bytes", after_size);
    println!("Size reduction: {} bytes", before_size - after_size);
}

fn main() -> Result<()> {
    let args = Args::parse();

    let mut db = IcingMetaDatabase::new(IcingTempDir::new("analysis-"))?;

    let initial_size = get_db_size(&db)?;

    println!("Initial database size: {} bytes", initial_size);

    let mut last_size = initial_size;

    let mut total_size_change = 0;

    for i in 1..=args.memories {
        let memory = create_memory(i, &args);

        db.add_memory(&memory, random::<u128>().to_string())?;

        let current_size = get_db_size(&db)?;

        let size_change = current_size - last_size;

        if args.verbose {
            println!(
                "Added memory {}: size change: {} bytes, total size: {} bytes",
                i, size_change, current_size
            );
        }

        last_size = current_size;

        total_size_change += size_change;
    }

    let average_size_per_memory =
        if args.memories > 0 { total_size_change / args.memories as usize } else { 0 };

    print_summary(&args, initial_size, last_size, total_size_change, average_size_per_memory);

    db.optimize()?;
    let optimized_size = get_db_size(&db)?;
    print_optimization_details(last_size, optimized_size);

    Ok(())
}
