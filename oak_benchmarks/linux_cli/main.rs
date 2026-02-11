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

//! Host-side runner for Linux VM benchmarks.
//!
//! This binary boots a Debian VM with a pre-installed benchmark server,
//! connects via gRPC, and runs benchmarks.

mod vm;

use std::{
    path::PathBuf,
    time::{Duration, Instant},
};

use anyhow::{Context, Result, anyhow};
use clap::Parser;
use cli_common::{
    BenchmarkMetrics, BenchmarkResult, DisplayBenchmarkType, OutputFormat, format_result,
    parse_benchmark_type,
};
use oak_benchmark_grpc::oak::benchmark::benchmark_client::BenchmarkClient;
use oak_benchmark_proto_rust::oak::benchmark::{
    BenchmarkType, RunBenchmarkRequest, RunBenchmarkResponse,
};
use tonic::transport::Channel;
use vm::{LinuxVm, VmConfig};

#[derive(Parser, Debug)]
#[command(name = "linux_cli")]
#[command(about = "Run benchmarks on a Linux VM")]
struct Args {
    /// Path to the VM image (qcow2).
    #[arg(long, value_name = "FILE")]
    vm_image: PathBuf,

    /// Path to run_vm.sh script (relative to runfiles when using bazel run).
    #[arg(long, default_value = "oak_benchmarks/linux_vm/run_vm.sh")]
    run_vm_script: PathBuf,

    /// Memory size for the VM.
    #[arg(long, default_value = "1G")]
    memory_size: String,

    /// Port for benchmark server (must match VM configuration).
    #[arg(long, default_value = "5000")]
    port: u16,

    /// Enable AMD SEV-SNP for the VM.
    #[arg(long)]
    enable_snp: bool,

    /// Timeout for VM boot in seconds.
    #[arg(long, default_value = "60")]
    boot_timeout: u64,

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

    /// Output format.
    #[arg(long, value_enum, default_value = "human")]
    output: OutputFormat,

    /// Don't shut down the VM after running (for debugging).
    #[arg(long)]
    keep_vm: bool,
}

/// Connect to the benchmark server and run a benchmark with retries.
///
/// Returns the response and the host-side elapsed time for the RPC.
async fn run_benchmark(
    addr: &str,
    request: RunBenchmarkRequest,
    timeout: Duration,
) -> Result<(RunBenchmarkResponse, Duration)> {
    let start = Instant::now();
    let mut last_error = None;

    loop {
        if start.elapsed() > timeout {
            return Err(
                last_error.unwrap_or_else(|| anyhow!("Timeout waiting for benchmark server"))
            );
        }

        let attempt_start = Instant::now();

        let channel_result = Channel::from_shared(format!("http://{}", addr))
            .context("Invalid address")?
            .connect()
            .await;

        match channel_result {
            Ok(channel) => {
                let mut client = BenchmarkClient::new(channel);
                match client.run_benchmark(request).await {
                    Ok(resp) => {
                        eprintln!("Connected!");
                        return Ok((resp.into_inner(), attempt_start.elapsed()));
                    }
                    Err(e) => {
                        log::debug!("RPC failed: {}, retrying...", e);
                        last_error = Some(anyhow!("RPC failed: {}", e));
                    }
                }
            }
            Err(e) => {
                log::debug!("Connection failed: {}, retrying...", e);
                last_error = Some(anyhow!("Connection failed: {}", e));
            }
        }

        tokio::time::sleep(Duration::from_secs(1)).await;
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    env_logger::init();
    let args = Args::parse();

    // Verify VM image exists.
    if !args.vm_image.exists() {
        return Err(anyhow!(
            "VM image not found: {}. See oak_benchmarks/linux_vm/README.md for setup.",
            args.vm_image.display()
        ));
    }

    // Boot the VM.
    eprintln!("Booting VM from {}...", args.vm_image.display());
    let vm_config = VmConfig {
        image: &args.vm_image,
        run_vm_script: &args.run_vm_script,
        memory_size: &args.memory_size,
        port: args.port,
        enable_snp: args.enable_snp,
    };
    let vm = LinuxVm::boot(&vm_config)?;

    eprintln!("Waiting for benchmark server on port {}...", args.port);

    // Run the benchmark.
    let request = RunBenchmarkRequest {
        benchmark_type: args.benchmark as i32,
        data_size: args.data_size,
        iterations: args.iterations,
        warmup_iterations: args.warmup_iterations,
    };
    let addr = format!("127.0.0.1:{}", args.port);
    let timeout = Duration::from_secs(args.boot_timeout);

    let (response, host_elapsed) = run_benchmark(&addr, request, timeout).await?;

    // Calculate metrics. The Linux runner provides elapsed_ns directly,
    // so tsc_freq is not needed (pass 0 as unused fallback).
    let metrics = BenchmarkMetrics::calculate(
        response.elapsed_tsc,
        response.elapsed_ns,
        response.iterations_completed,
        response.bytes_processed,
        0, // tsc_freq unused — Linux runner provides elapsed_ns
    );
    let result = BenchmarkResult {
        benchmark_name: DisplayBenchmarkType(args.benchmark).to_string(),
        data_size: args.data_size,
        iterations_completed: response.iterations_completed,
        elapsed_tsc: response.elapsed_tsc,
        elapsed_ns: metrics.elapsed_ns,
        bytes_processed: response.bytes_processed,
        status: response.status,
    };
    print!("{}", format_result(&result, &metrics, args.output));

    // Print host timing for Human format.
    if matches!(args.output, OutputFormat::Human) {
        println!("Host timing (wall clock):");
        println!("  Elapsed time:  {:.3} ms", host_elapsed.as_secs_f64() * 1000.0);
    }

    // Shutdown VM.
    if !args.keep_vm {
        eprintln!("Shutting down VM...");
        vm.shutdown()?;
    } else {
        eprintln!("Keeping VM running (--keep-vm). PID: {:?}", vm.pid());
        std::mem::forget(vm);
    }

    Ok(())
}
