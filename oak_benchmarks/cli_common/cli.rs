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

pub use benchmark::DEFAULT_BENCHMARK_SEED;
use clap::ValueEnum;
use oak_benchmark_proto_rust::oak::benchmark::BenchmarkType;

/// What a benchmark's `bytes_processed` counts.
///
/// Every benchmark that moves data populates the field, but it does not count
/// the same quantity in each of them, so a byte-rate figure is only comparable
/// between benchmarks sharing a variant. Reporting code uses this to label the
/// figure and to decide whether cycles per byte is meaningful at all; without
/// the label a reader has no way to tell that the hash rows and the allocator
/// rows are measuring different things.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ByteSemantics {
    /// Bytes fed through a primitive, counted once per pass over the message.
    ///
    /// The only variant matching the convention behind published
    /// cycles-per-byte figures, so it is the only one for which that metric
    /// is emitted. See the units eBACS reports at <https://bench.cr.yp.to/results-hash.html>.
    Message,

    /// Bytes of the message a signature covers.
    ///
    /// Labelled the same way as [`ByteSemantics::Message`], but no per-byte
    /// figure is emitted: the message is hashed once and the cost is dominated
    /// by a fixed-size group operation, so dividing by the message length
    /// describes the length chosen for the benchmark rather than the
    /// primitive. At the 32 bytes the suite uses it is off by two orders of
    /// magnitude.
    Signed,

    /// Bytes of key and value stored or retrieved by one map operation.
    ///
    /// Excludes hashing, probing and table overhead, so it understates the
    /// memory traffic the benchmark actually causes by a large factor.
    Payload,

    /// Bytes requested from the allocator, whether or not they were written.
    ///
    /// An allocator can hand back an untouched mapping, so this can exceed the
    /// machine's memory bandwidth and is not a throughput in any physical
    /// sense.
    Requested,

    /// Bytes written by the program.
    ///
    /// The memory system moves a whole cache line per write, so for a benchmark
    /// writing single bytes at scattered offsets this understates the traffic
    /// by up to the line size.
    Written,

    /// The benchmark moves no data and reports no byte rate.
    None,
}

impl ByteSemantics {
    /// Stable token for machine-readable output.
    pub fn name(&self) -> &'static str {
        match self {
            ByteSemantics::Message => "message",
            ByteSemantics::Signed => "signed",
            ByteSemantics::Payload => "payload",
            ByteSemantics::Requested => "requested",
            ByteSemantics::Written => "written",
            ByteSemantics::None => "none",
        }
    }

    /// Short phrase naming what the bytes are, for use next to a rate.
    pub fn label(&self) -> &'static str {
        match self {
            ByteSemantics::Message => "message bytes",
            ByteSemantics::Signed => "message bytes",
            ByteSemantics::Payload => "key+value bytes",
            ByteSemantics::Requested => "bytes requested from the allocator",
            ByteSemantics::Written => "bytes written",
            ByteSemantics::None => "no bytes",
        }
    }

    /// Whether a cycles-per-byte figure is comparable with published numbers.
    pub fn supports_per_byte(&self) -> bool {
        matches!(self, ByteSemantics::Message)
    }
}

/// One selectable benchmark: its CLI spelling, its wire type, how it is named
/// in a report, and what its byte count means.
///
/// Kept as a single table so that the parser, the `--help` text, the error
/// message, the report label and the byte semantics cannot drift apart. They
/// previously lived in two tables fifteen lines apart.
#[derive(Debug, Clone, Copy)]
pub struct BenchmarkInfo {
    /// Canonical spelling accepted on the command line.
    pub cli_name: &'static str,
    /// Wire enum sent to the guest.
    pub benchmark_type: BenchmarkType,
    /// How the benchmark is named in human-readable output.
    pub display_name: &'static str,
    /// What this benchmark's `bytes_processed` counts.
    pub bytes: ByteSemantics,
}

/// Every benchmark type selectable from the command line.
pub const BENCHMARKS: &[BenchmarkInfo] = &[
    info("sha256", BenchmarkType::Sha256, "SHA-256", ByteSemantics::Message),
    info("sha512", BenchmarkType::Sha512, "SHA-512", ByteSemantics::Message),
    info("sha3-256", BenchmarkType::Sha3256, "SHA3-256", ByteSemantics::Message),
    info("sha3-512", BenchmarkType::Sha3512, "SHA3-512", ByteSemantics::Message),
    info("p256-sign", BenchmarkType::P256Sign, "P-256 Sign", ByteSemantics::Signed),
    info("p256-verify", BenchmarkType::P256Verify, "P-256 Verify", ByteSemantics::Signed),
    info("ed25519-sign", BenchmarkType::Ed25519Sign, "Ed25519 Sign", ByteSemantics::Signed),
    info(
        "ed25519-verify",
        BenchmarkType::Ed25519Verify,
        "Ed25519 Verify (strict)",
        ByteSemantics::Signed,
    ),
    info(
        "aes256gcm-seal",
        BenchmarkType::Aes256GcmSeal,
        "AES-256-GCM Seal",
        ByteSemantics::Message,
    ),
    info(
        "aes256gcm-open",
        BenchmarkType::Aes256GcmOpen,
        "AES-256-GCM Open",
        ByteSemantics::Message,
    ),
    info("memory-insert", BenchmarkType::MemoryInsert, "Memory Insert", ByteSemantics::Payload),
    info("memory-lookup", BenchmarkType::MemoryLookup, "Memory Lookup", ByteSemantics::Payload),
    info("memory-churn", BenchmarkType::MemoryChurn, "Memory Churn", ByteSemantics::Payload),
    info("array-update", BenchmarkType::ArrayUpdate, "Array Update", ByteSemantics::Written),
    info("alloc-churn", BenchmarkType::AllocChurn, "Alloc Churn", ByteSemantics::Requested),
    info("pointer-chase", BenchmarkType::PointerChase, "Pointer Chase", ByteSemantics::None),
    info("page-touch", BenchmarkType::PageTouch, "Page Touch", ByteSemantics::None),
    info("null-syscall", BenchmarkType::NullSyscall, "Null Syscall", ByteSemantics::None),
    info(
        "syscall-control",
        BenchmarkType::SyscallControl,
        "Syscall Control (no syscall)",
        ByteSemantics::None,
    ),
    info("debug", BenchmarkType::Debug, "Debug", ByteSemantics::None),
];

/// Table constructor, so the entries above stay one line each.
const fn info(
    cli_name: &'static str,
    benchmark_type: BenchmarkType,
    display_name: &'static str,
    bytes: ByteSemantics,
) -> BenchmarkInfo {
    BenchmarkInfo { cli_name, benchmark_type, display_name, bytes }
}

/// Look up a benchmark's table entry.
///
/// `None` only for [`BenchmarkType::Unspecified`], which is not selectable.
pub fn benchmark_info(benchmark_type: BenchmarkType) -> Option<&'static BenchmarkInfo> {
    BENCHMARKS.iter().find(|info| info.benchmark_type == benchmark_type)
}

/// What a benchmark's byte count means. Defaults to [`ByteSemantics::None`] for
/// an unrecognised type, so an unknown benchmark reports no byte rate rather
/// than an unlabelled one.
pub fn byte_semantics(benchmark_type: BenchmarkType) -> ByteSemantics {
    benchmark_info(benchmark_type).map_or(ByteSemantics::None, |info| info.bytes)
}

/// Normalise a CLI spelling: lowercase, and treat `-` and `_` as equivalent.
fn normalize(s: &str) -> String {
    s.to_lowercase().replace('-', "_")
}

/// Parse a benchmark type from a CLI string.
///
/// Supports kebab-case and snake_case variants for convenience.
pub fn parse_benchmark_type(s: &str) -> Result<BenchmarkType, String> {
    let wanted = normalize(s);
    for info in BENCHMARKS {
        if normalize(info.cli_name) == wanted {
            return Ok(info.benchmark_type);
        }
    }
    // A few extra spellings that do not deserve their own table entry.
    match wanted.as_str() {
        "sha3256" => return Ok(BenchmarkType::Sha3256),
        "sha3512" => return Ok(BenchmarkType::Sha3512),
        "eddsa_sign" => return Ok(BenchmarkType::Ed25519Sign),
        "eddsa_verify" => return Ok(BenchmarkType::Ed25519Verify),
        _ => {}
    }

    let valid: Vec<&str> = BENCHMARKS.iter().map(|info| info.cli_name).collect();
    Err(format!("unknown benchmark type '{}'; valid options: {}", s, valid.join(", ")))
}

/// Display wrapper for BenchmarkType with human-readable names.
pub struct DisplayBenchmarkType(pub BenchmarkType);

impl fmt::Display for DisplayBenchmarkType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = benchmark_info(self.0).map_or("Unspecified", |info| info.display_name);
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The benchmarks the README promises a per-byte figure for. A signature
    /// over a fixed-size digest is deliberately not among them; see
    /// [`ByteSemantics::Signed`].
    const PER_BYTE: &[&str] =
        &["sha256", "sha512", "sha3-256", "sha3-512", "aes256gcm-seal", "aes256gcm-open"];

    #[test]
    fn only_hash_and_aead_benchmarks_report_a_per_byte_figure() {
        let actual: Vec<&str> = BENCHMARKS
            .iter()
            .filter(|info| info.bytes.supports_per_byte())
            .map(|info| info.cli_name)
            .collect();
        assert_eq!(actual, PER_BYTE);
    }

    #[test]
    fn signed_bytes_read_as_message_bytes_but_are_a_distinct_token() {
        assert_eq!(ByteSemantics::Signed.label(), ByteSemantics::Message.label());
        assert_ne!(ByteSemantics::Signed.name(), ByteSemantics::Message.name());
    }
}
