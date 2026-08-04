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

//! Benchmark result metrics and formatting.

pub use benchmark::cpu::CpuFeatures;

use crate::{cli::OutputFormat, tsc::tsc_to_nanos};

/// Calculated metrics from a benchmark response.
#[derive(Debug, Clone, Copy)]
pub struct BenchmarkMetrics {
    /// Elapsed time in nanoseconds.
    ///
    /// Taken directly from the guest where a clock exists, otherwise derived
    /// from `elapsed_tsc` using the calibrated frequency.
    pub elapsed_ns: u64,
    /// Throughput in bytes per second (base unit).
    pub throughput_bps: f64,
    /// Operations (hashes, signatures, lookups, ...) per second.
    pub ops_per_sec: f64,
}

impl BenchmarkMetrics {
    /// Calculate metrics from raw benchmark data.
    ///
    /// Both platforms now report `elapsed_tsc`. `elapsed_ns` is additionally
    /// reported by the Linux baseline, which has a real clock; when present it
    /// is preferred over converting from ticks, since it involves no
    /// calibration at all.
    pub fn calculate(
        elapsed_tsc: u64,
        elapsed_ns: u64,
        iterations_completed: u32,
        bytes_processed: u64,
        tsc_freq: u64,
    ) -> Self {
        // Use elapsed_ns directly if available, otherwise convert from TSC.
        let elapsed_ns =
            if elapsed_ns > 0 { elapsed_ns } else { tsc_to_nanos(elapsed_tsc, tsc_freq) };

        let throughput_bps = if elapsed_ns > 0 {
            bytes_processed as f64 / (elapsed_ns as f64 / 1_000_000_000.0)
        } else {
            0.0
        };

        let ops_per_sec = if elapsed_ns > 0 {
            (iterations_completed as f64) / (elapsed_ns as f64 / 1_000_000_000.0)
        } else {
            0.0
        };

        Self { elapsed_ns, throughput_bps, ops_per_sec }
    }

    /// Get throughput in MB/s for display purposes.
    pub fn throughput_mbps(&self) -> f64 {
        self.throughput_bps / 1_000_000.0
    }
}

/// Common fields needed for formatting benchmark results.
/// Proto-agnostic to work with both service::* and oak_proto_rust::* types.
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub benchmark_name: String,
    pub data_size: u32,
    pub iterations_completed: u32,
    pub elapsed_tsc: u64,
    pub elapsed_ns: u64,
    pub bytes_processed: u64,
    pub status: u32,
    /// Actual working set size used by the guest, in bytes.
    pub working_set_size: u64,
    /// Checksum over the benchmark output.
    ///
    /// Must match between the enclave and the baseline for the same benchmark,
    /// seed and parameters. A mismatch means the two sides did different work
    /// and the comparison is invalid.
    pub checksum: u64,
    /// Packed [`CpuFeatures`]: compile-time features, `CPUID` features and the
    /// runtime-dispatch flag. Layout is defined by `CpuFeatures::to_wire`.
    pub cpu_features: u32,
}

/// Human-readable description of a guest status code.
///
/// Delegates to the benchmark crate so the mapping has a single definition.
pub fn describe_status(status: u32) -> &'static str {
    benchmark::BenchmarkError::describe(status)
}

/// Convert a guest status code into a `Result`.
///
/// The host CLIs must call this before formatting a response. A failed
/// benchmark returns an all-zero response, and treating that as a real
/// measurement produced both nonsense results and, previously, a
/// divide-by-zero panic that hid the underlying error entirely.
pub fn check_status(status: u32) -> Result<(), String> {
    if status == 0 {
        Ok(())
    } else {
        Err(format!("guest benchmark failed with status {status}: {}", describe_status(status)))
    }
}

/// Format benchmark results for output.
pub fn format_result(
    result: &BenchmarkResult,
    metrics: &BenchmarkMetrics,
    format: OutputFormat,
) -> String {
    match format {
        OutputFormat::Human => {
            format!(
                "\n=== Benchmark Results ===\n\
                 Benchmark:           {}\n\
                 Data size:           {} bytes\n\
                 Iterations:          {}\n\
                 Working set:         {} bytes\n\
                 Guest elapsed (TSC): {} ticks\n\
                 Guest elapsed:       {:.3} ms\n\
                 Bytes processed:     {}\n\
                 Throughput:          {:.2} MB/s\n\
                 Operations/sec:      {:.0}\n\
                 Checksum:            0x{:016x}\n\
                 CPU features:        {:#}\n\
                 Status:              {}\n",
                result.benchmark_name,
                result.data_size,
                result.iterations_completed,
                result.working_set_size,
                result.elapsed_tsc,
                metrics.elapsed_ns as f64 / 1_000_000.0,
                result.bytes_processed,
                metrics.throughput_mbps(),
                metrics.ops_per_sec,
                result.checksum,
                CpuFeatures::from_wire(result.cpu_features),
                if result.status == 0 { "OK" } else { "ERROR" },
            )
        }
        OutputFormat::Csv => {
            // Use base units (bytes/s) in machine-readable formats.
            format!(
                "{},{},{},{},{},{},{:.0},{:.0},{},{},{},{}\n",
                result.benchmark_name,
                result.data_size,
                result.iterations_completed,
                result.elapsed_tsc,
                metrics.elapsed_ns,
                result.bytes_processed,
                metrics.throughput_bps,
                metrics.ops_per_sec,
                result.working_set_size,
                result.checksum,
                result.cpu_features,
                result.status,
            )
        }
        OutputFormat::Json => {
            // Use base units (bytes/s) in machine-readable formats.
            format!(
                r#"{{"benchmark":"{}","data_size":{},"iterations":{},"elapsed_tsc":{},"elapsed_ns":{},"bytes_processed":{},"throughput_bps":{:.0},"ops_per_sec":{:.0},"working_set_size":{},"checksum":{},"cpu_features":{},"status":{}}}"#,
                result.benchmark_name,
                result.data_size,
                result.iterations_completed,
                result.elapsed_tsc,
                metrics.elapsed_ns,
                result.bytes_processed,
                metrics.throughput_bps,
                metrics.ops_per_sec,
                result.working_set_size,
                result.checksum,
                result.cpu_features,
                result.status,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn elapsed_ns_is_preferred_over_conversion() {
        // A deliberately wrong frequency must not affect the reported time
        // when the guest supplied real nanoseconds.
        let m = BenchmarkMetrics::calculate(999_999_999, 2_000_000, 10, 0, 1);
        assert_eq!(m.elapsed_ns, 2_000_000);
    }

    #[test]
    fn zero_everything_does_not_panic_or_divide_by_zero() {
        let m = BenchmarkMetrics::calculate(0, 0, 0, 0, 0);
        assert_eq!(m.elapsed_ns, 0);
        assert_eq!(m.throughput_bps, 0.0);
        assert_eq!(m.ops_per_sec, 0.0);
    }
}
