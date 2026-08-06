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

//! Host-side benchmark runner for Oak Restricted Kernel.
//!
//! This binary launches the benchmark enclave app, sends benchmark commands,
//! and collects results using the micro_rpc Benchmark service.

use std::time::Instant;

use anyhow::{Context, Result};
use clap::Parser;
use cli_common::{
    BenchmarkMetrics, CpuFeatures, DEFAULT_BENCHMARK_SEED, DisplayBenchmarkType, OutputFormat,
    check_status, csv_header, detect_tsc_freq, format_result, parse_benchmark_type,
    sanitize_detail,
};
use oak_benchmark_proto_rust::oak::benchmark::{BenchmarkType, RunBenchmarkRequest};
use oak_launcher_utils::launcher;
use service::oak::benchmark::BenchmarkAsyncClient;

#[derive(Parser, Debug)]
#[command(name = "oak_cli")]
#[command(about = "Run benchmarks on Oak Restricted Kernel")]
struct Args {
    /// Launcher parameters.
    #[clap(flatten)]
    launcher_params: launcher::Params,

    /// Benchmark to run.
    #[arg(long, value_parser = parse_benchmark_type, default_value = "sha256")]
    benchmark: BenchmarkType,

    /// Data size in bytes for the benchmark.
    #[arg(long, default_value = "1024")]
    data_size: u32,

    /// Number of iterations to run (timed).
    #[arg(long, default_value = "10000")]
    iterations: u32,

    /// Number of warmup iterations to run before measurement (not timed).
    /// Warmup helps the CPU's branch predictor and caches reach steady-state.
    #[arg(long, default_value = "1000")]
    warmup_iterations: u32,

    /// Seed for deterministic benchmark data.
    ///
    /// Must match the value used for the Linux baseline, otherwise the two
    /// runs process different data and are not comparable. Defaults to a
    /// fixed constant shared by both CLIs.
    #[arg(long, default_value_t = DEFAULT_BENCHMARK_SEED)]
    seed: u64,

    /// Working set size in bytes for the memory benchmarks (0 = guest default).
    #[arg(long, default_value = "0")]
    working_set_size: u64,

    /// TSC frequency in Hz (for converting TSC ticks to time).
    /// If not specified, it is measured against the monotonic clock.
    #[arg(long)]
    tsc_freq: Option<u64>,

    /// Emit a CSV header line before the result row.
    #[arg(long, default_value = "false")]
    csv_header: bool,

    /// Output format.
    #[arg(long, value_enum, default_value = "human")]
    output: OutputFormat,
}

#[tokio::main]
async fn main() -> Result<()> {
    let args = Args::parse();
    env_logger::init();

    log::info!("Starting Oak Benchmark Host Runner");
    log::info!("Benchmark: {:?}", args.benchmark);
    log::info!("Data size: {} bytes", args.data_size);
    log::info!("Iterations: {}", args.iterations);

    // Launch the enclave.
    log::info!("Launching enclave...");
    let (guest_instance, connector_handle) = launcher::launch(args.launcher_params)
        .await
        .map_err(|e| anyhow::anyhow!("Failed to launch enclave: {}", e))?;

    log::info!("Enclave launched");

    // Create the micro_rpc async client.
    let mut client = BenchmarkAsyncClient::new(connector_handle);

    // Create the benchmark request for micro_rpc (uses service types).
    // The wire format is identical to oak_proto_rust types.
    let request = RunBenchmarkRequest {
        benchmark_type: args.benchmark as i32,
        data_size: args.data_size,
        iterations: args.iterations,
        warmup_iterations: args.warmup_iterations,
        seed: Some(args.seed),
        working_set_size: args.working_set_size,
    };

    log::info!("Sending benchmark request...");
    let host_start = Instant::now();

    // Call the RunBenchmark RPC.
    let response = client
        .run_benchmark(&request)
        .await
        .map_err(|e| anyhow::anyhow!("Failed to invoke benchmark RPC: {:?}", e))?
        .map_err(|e| anyhow::anyhow!("Benchmark RPC returned error: {:?}", e))?;

    let host_elapsed = host_start.elapsed();

    // Abort before formatting: a failed benchmark returns an all-zero
    // response, which would otherwise be printed as a plausible-looking row of
    // zeros. Tear the enclave down first so we do not leak a QEMU process.
    if let Err(message) = check_status(response.status) {
        guest_instance.kill().await.context("terminating enclave after a failed benchmark")?;
        anyhow::bail!(message);
    }

    // Calculate metrics using shared cli_common utilities.
    let tsc_freq = args.tsc_freq.unwrap_or_else(|| {
        let detected = detect_tsc_freq();
        log::info!(
            "detected TSC frequency: {} Hz (source: {})",
            detected.hz(),
            detected.source_description()
        );
        if !detected.is_trustworthy() {
            log::warn!(
                "TSC frequency was not measured directly ({}); nanosecond and MB/s figures may \
                 be scaled incorrectly, prefer the cycles/op column",
                detected.source_description()
            );
        }
        detected.hz()
    });
    let metrics = BenchmarkMetrics::calculate(
        response.elapsed_tsc,
        response.elapsed_ns,
        response.iterations_completed,
        response.bytes_processed,
        tsc_freq,
    );

    log::info!("guest CPU features: {}", CpuFeatures::from_wire(response.cpu_features));

    // Output results using cli_common formatter.
    let result = cli_common::BenchmarkResult {
        benchmark_name: DisplayBenchmarkType(args.benchmark).to_string(),
        data_size: args.data_size,
        iterations_completed: response.iterations_completed,
        elapsed_tsc: response.elapsed_tsc,
        elapsed_ns: metrics.elapsed_ns,
        bytes_processed: response.bytes_processed,
        status: response.status,
        working_set_size: response.working_set_size,
        checksum: response.checksum,
        cpu_features: response.cpu_features,
        detail: sanitize_detail(&response.detail),
    };
    if args.csv_header && matches!(args.output, OutputFormat::Csv) {
        print!("{}", csv_header());
    }
    let output = format_result(&result, &metrics, args.output);
    print!("{}", output);

    // Print host timing for Human format.
    if matches!(args.output, OutputFormat::Human) {
        println!("Host timing (wall clock, includes enclave RPC round trip):");
        println!("  Elapsed time:  {:.3} ms", host_elapsed.as_secs_f64() * 1000.0);
    }

    // Clean up.
    log::info!("terminating enclave");
    guest_instance.kill().await?;

    Ok(())
}
