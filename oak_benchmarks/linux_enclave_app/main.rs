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

//! Linux benchmark runner.
//!
//! This binary runs benchmarks natively on Linux as a baseline for comparison
//! with enclave execution.
//!
//! Two modes:
//!   - **Standalone**: runs a benchmark locally and prints results to stdout.
//!   - **Server**: starts a gRPC server so that `linux_cli` can send benchmark
//!     requests remotely (e.g. to a VM with SEV-SNP enabled).

use benchmark::{BenchmarkService, NativeTimer};
use clap::Parser;
use cli_common::{
    BenchmarkMetrics, BenchmarkResult, DisplayBenchmarkType, OutputFormat, format_result,
    parse_benchmark_type,
};
use oak_benchmark_proto_rust::oak::benchmark::{BenchmarkType, RunBenchmarkRequest};

#[derive(Parser, Debug)]
#[command(name = "linux_benchmark_runner")]
#[command(about = "Run benchmarks natively on Linux (baseline comparison)")]
struct Args {
    /// Start a gRPC server on this port instead of running a benchmark locally.
    /// Used by linux_cli to send benchmark requests to a VM.
    #[arg(long)]
    serve: Option<u16>,

    /// Benchmark to run (standalone mode only).
    #[arg(long, value_parser = parse_benchmark_type, default_value = "debug")]
    benchmark: BenchmarkType,

    /// Data size in bytes for the benchmark.
    #[arg(long, default_value = "1024")]
    data_size: u32,

    /// Number of iterations to run (timed).
    #[arg(long, default_value = "10000")]
    iterations: u32,

    /// Number of warmup iterations to run before measurement (not timed).
    #[arg(long, default_value = "1000")]
    warmup_iterations: u32,

    /// Output format (standalone mode only).
    #[arg(long, value_enum, default_value = "human")]
    output: OutputFormat,

    /// Seed for random data generation (0 = random seed from time).
    #[arg(long, default_value = "0")]
    seed: u64,
}

// ── gRPC server implementation ──

mod grpc_server {
    use std::sync::Mutex;

    use benchmark::{BenchmarkService, NativeTimer};
    use oak_benchmark_grpc::oak::benchmark::benchmark_server::Benchmark;
    use oak_benchmark_proto_rust::oak::benchmark::{RunBenchmarkRequest, RunBenchmarkResponse};
    use tonic::{Request, Response, Status};

    pub struct BenchmarkGrpcService {
        service: Mutex<BenchmarkService<NativeTimer>>,
    }

    impl BenchmarkGrpcService {
        pub fn new(seed: u64) -> Self {
            Self { service: Mutex::new(BenchmarkService::new(seed)) }
        }
    }

    #[tonic::async_trait]
    impl Benchmark for BenchmarkGrpcService {
        async fn run_benchmark(
            &self,
            request: Request<RunBenchmarkRequest>,
        ) -> Result<Response<RunBenchmarkResponse>, Status> {
            let req = request.into_inner();
            let response = self
                .service
                .lock()
                .map_err(|e| Status::internal(format!("Lock error: {}", e)))?
                .handle_request(req);
            Ok(Response::new(response))
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    if let Some(port) = args.serve {
        // gRPC server mode.
        run_server(port, args.seed).await
    } else {
        // Standalone mode.
        run_standalone(&args);
        Ok(())
    }
}

async fn run_server(port: u16, seed: u64) -> Result<(), Box<dyn std::error::Error>> {
    use oak_benchmark_grpc::oak::benchmark::benchmark_server::BenchmarkServer;

    let seed = if seed == 0 {
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
            as u64
    } else {
        seed
    };

    let addr = format!("0.0.0.0:{}", port).parse()?;
    let service = grpc_server::BenchmarkGrpcService::new(seed);

    eprintln!("Benchmark gRPC server listening on {}", addr);

    tonic::transport::Server::builder()
        .add_service(BenchmarkServer::new(service))
        .serve(addr)
        .await?;

    Ok(())
}

/// Run the benchmark locally and print results.
fn run_standalone(args: &Args) {
    let seed = if args.seed == 0 {
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
            as u64
    } else {
        args.seed
    };

    let service = BenchmarkService::<NativeTimer>::new(seed);

    let request = RunBenchmarkRequest {
        benchmark_type: args.benchmark as i32,
        data_size: args.data_size,
        iterations: args.iterations,
        warmup_iterations: args.warmup_iterations,
    };

    let response = service.handle_request(request);

    // Use cli_common for metrics calculation and formatting.
    let metrics = BenchmarkMetrics::calculate(
        response.elapsed_tsc,
        response.elapsed_ns,
        response.iterations_completed,
        response.bytes_processed,
        0, // tsc_freq — not used on Linux
    );
    let result = BenchmarkResult {
        benchmark_name: DisplayBenchmarkType(args.benchmark).to_string(),
        data_size: args.data_size,
        iterations_completed: response.iterations_completed,
        elapsed_tsc: response.elapsed_tsc,
        elapsed_ns: response.elapsed_ns,
        bytes_processed: response.bytes_processed,
        status: response.status,
    };
    print!("{}", format_result(&result, &metrics, args.output));
}
