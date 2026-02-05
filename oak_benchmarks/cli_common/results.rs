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

use crate::{cli::OutputFormat, tsc::tsc_to_nanos};

/// Calculated metrics from a benchmark response.
#[derive(Debug, Clone, Copy)]
pub struct BenchmarkMetrics {
    /// Elapsed time in nanoseconds.
    pub elapsed_ns: u64,
    /// Throughput in bytes per second (base unit).
    pub throughput_bps: f64,
    /// Operations (hashes) per second.
    pub ops_per_sec: f64,
}

impl BenchmarkMetrics {
    /// Calculate metrics from raw benchmark data.
    ///
    /// This is proto-type agnostic - works with any source of benchmark data.
    pub fn calculate(
        elapsed_tsc: u64,
        iterations_completed: u32,
        bytes_processed: u64,
        tsc_freq: u64,
    ) -> Self {
        let elapsed_ns = tsc_to_nanos(elapsed_tsc, tsc_freq);

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
    pub bytes_processed: u64,
    pub status: u32,
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
                 Guest elapsed:       {:.3} ms\n\
                 Bytes processed:     {}\n\
                 Throughput:          {:.2} MB/s\n\
                 Operations/sec:      {:.0}\n\
                 Status:              {}\n",
                result.benchmark_name,
                result.data_size,
                result.iterations_completed,
                metrics.elapsed_ns as f64 / 1_000_000.0,
                result.bytes_processed,
                metrics.throughput_mbps(),
                metrics.ops_per_sec,
                if result.status == 0 { "OK" } else { "ERROR" },
            )
        }
        OutputFormat::Csv => {
            // Use base units (bytes/s) in machine-readable formats
            format!(
                "{},{},{},{},{:.0},{:.0},{}\n",
                result.benchmark_name,
                result.data_size,
                result.iterations_completed,
                result.elapsed_tsc,
                metrics.throughput_bps,
                metrics.ops_per_sec,
                result.status,
            )
        }
        OutputFormat::Json => {
            // Use base units (bytes/s) in machine-readable formats
            format!(
                r#"{{"benchmark":"{}","data_size":{},"iterations":{},"elapsed_tsc":{},"elapsed_ns":{},"bytes_processed":{},"throughput_bps":{:.0},"ops_per_sec":{:.0},"status":{}}}"#,
                result.benchmark_name,
                result.data_size,
                result.iterations_completed,
                result.elapsed_tsc,
                metrics.elapsed_ns,
                result.bytes_processed,
                metrics.throughput_bps,
                metrics.ops_per_sec,
                result.status,
            )
        }
    }
}
