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

//! CLI argument parsing utilities for Oak benchmarks.

use std::fmt;

use clap::ValueEnum;
use oak_benchmark_proto_rust::oak::benchmark::BenchmarkType;

/// Parse a benchmark type from a CLI string.
///
/// Supports kebab-case and snake_case variants for convenience.
pub fn parse_benchmark_type(s: &str) -> Result<BenchmarkType, String> {
    match s.to_lowercase().replace('-', "_").as_str() {
        "sha256" => Ok(BenchmarkType::Sha256),
        "sha512" => Ok(BenchmarkType::Sha512),
        "sha3_256" | "sha3256" => Ok(BenchmarkType::Sha3256),
        "sha3_512" | "sha3512" => Ok(BenchmarkType::Sha3512),
        "p256_sign" | "p256sign" => Ok(BenchmarkType::P256Sign),
        "memory_insert" => Ok(BenchmarkType::MemoryInsert),
        "memory_lookup" => Ok(BenchmarkType::MemoryLookup),
        "array_update" => Ok(BenchmarkType::ArrayUpdate),
        "debug" => Ok(BenchmarkType::Debug),
        _ => Err(format!(
            "Unknown benchmark type: '{}'. Valid options: sha256, sha512, sha3-256, sha3-512, \
             p256-sign, memory-insert, memory-lookup, array-update, debug",
            s
        )),
    }
}

/// Display wrapper for BenchmarkType with human-readable names.
pub struct DisplayBenchmarkType(pub BenchmarkType);

impl fmt::Display for DisplayBenchmarkType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self.0 {
            BenchmarkType::Sha256 => "SHA-256",
            BenchmarkType::Sha512 => "SHA-512",
            BenchmarkType::Sha3256 => "SHA3-256",
            BenchmarkType::Sha3512 => "SHA3-512",
            BenchmarkType::P256Sign => "P-256 Sign",
            BenchmarkType::MemoryInsert => "Memory Insert",
            BenchmarkType::MemoryLookup => "Memory Lookup",
            BenchmarkType::ArrayUpdate => "Array Update",
            BenchmarkType::Debug => "Debug",
            BenchmarkType::Unspecified => "Unspecified",
        };
        write!(f, "{}", name)
    }
}

/// Output format for benchmark results.
#[derive(Debug, Clone, Copy, ValueEnum, Default)]
pub enum OutputFormat {
    /// Human-readable output.
    #[default]
    Human,
    /// CSV format for spreadsheets.
    Csv,
    /// JSON format for programmatic parsing.
    Json,
}
