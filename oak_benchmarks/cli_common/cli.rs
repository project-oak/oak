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

/// Every benchmark type selectable from the command line, with its canonical
/// CLI spelling.
///
/// Kept as a single table so that the parser, the `--help` text and the error
/// message cannot drift apart.
pub const BENCHMARK_TYPE_NAMES: &[(&str, BenchmarkType)] = &[
    ("sha256", BenchmarkType::Sha256),
    ("sha512", BenchmarkType::Sha512),
    ("sha3-256", BenchmarkType::Sha3256),
    ("sha3-512", BenchmarkType::Sha3512),
    ("p256-sign", BenchmarkType::P256Sign),
    ("memory-insert", BenchmarkType::MemoryInsert),
    ("memory-lookup", BenchmarkType::MemoryLookup),
    ("array-update", BenchmarkType::ArrayUpdate),
    ("alloc-churn", BenchmarkType::AllocChurn),
    ("debug", BenchmarkType::Debug),
];

/// Normalise a CLI spelling: lowercase, and treat `-` and `_` as equivalent.
fn normalize(s: &str) -> String {
    s.to_lowercase().replace('-', "_")
}

/// Parse a benchmark type from a CLI string.
///
/// Supports kebab-case and snake_case variants for convenience.
pub fn parse_benchmark_type(s: &str) -> Result<BenchmarkType, String> {
    let wanted = normalize(s);
    for (name, benchmark_type) in BENCHMARK_TYPE_NAMES {
        if normalize(name) == wanted {
            return Ok(*benchmark_type);
        }
    }
    // A few extra spellings that do not deserve their own table entry.
    match wanted.as_str() {
        "sha3256" => return Ok(BenchmarkType::Sha3256),
        "sha3512" => return Ok(BenchmarkType::Sha3512),
        _ => {}
    }

    let valid: Vec<&str> = BENCHMARK_TYPE_NAMES.iter().map(|(name, _)| *name).collect();
    Err(format!("unknown benchmark type '{}'; valid options: {}", s, valid.join(", ")))
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
            BenchmarkType::AllocChurn => "Alloc Churn",
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
