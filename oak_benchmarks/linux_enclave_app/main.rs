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

//! Linux benchmark runner, the baseline for enclave execution.
//!
//! Standalone mode runs a benchmark locally and prints the result. Server mode
//! starts a gRPC server for `linux_cli`, so the benchmark can run in a VM with
//! SEV-SNP enabled.
//!
//! To compare a result here with one from `oak_cli`, both sides need the same
//! `--seed`, sizes and iteration counts, and must report the same `checksum`
//! and `cpu_features`. The defaults already satisfy this.

use benchmark::{BenchmarkService, DEFAULT_BENCHMARK_SEED, NativeTimer, NullSyscall};
use clap::Parser;
use cli_common::{
    BenchmarkMetrics, BenchmarkResult, CpuFeatures, DisplayBenchmarkType, OutputFormat,
    RepeatedRun, Repetition, TscFreq, byte_semantics, check_status, csv_header, format_repeated,
    format_result, parse_benchmark_type, repeated_csv_header, sanitize_detail,
};
use oak_benchmark_proto_rust::oak::benchmark::{BenchmarkType, RunBenchmarkRequest};

/// The syscall the null syscall benchmark invokes on Linux.
///
/// `getppid()` is lmbench's choice for `lat_syscall null`, so almost all of the
/// measured cost is entry and exit. It is not the syscall the enclave measures;
/// the benchmark crate's `syscall` module explains why.
///
/// Issued as raw assembly because whether the libc wrapper caches the result
/// has changed over time (glibc cached `getpid()` until 2.25), and a cached
/// call would measure nothing. Syscall number 110 is `getppid` on x86-64, per
/// <https://github.com/torvalds/linux/blob/master/arch/x86/entry/syscalls/syscall_64.tbl>,
/// and the clobber set is the one in
/// <https://man7.org/linux/man-pages/man2/syscall.2.html>.
struct Getppid;

#[cfg(not(target_arch = "x86_64"))]
compile_error!("the null syscall probe is written in x86-64 assembly");

impl NullSyscall for Getppid {
    fn invoke(&self) -> i64 {
        const SYS_GETPPID: i64 = 110;
        let result: i64;
        // Safety: the kernel reads no memory through this call, so there is no
        // pointer to get wrong, and `rax`, `rcx` and `r11` are the full clobber
        // set for `syscall` on x86-64; all three are declared. `nostack` holds
        // because `syscall` switches to the kernel stack through `MSR_LSTAR`
        // and `swapgs`, and the kernel never writes below the user `rsp`, so
        // the red zone survives. `preserves_flags` holds because `SYSCALL`
        // saves `RFLAGS` into `r11` and `SYSRET` restores it.
        unsafe {
            std::arch::asm!(
                "syscall",
                inlateout("rax") SYS_GETPPID => result,
                lateout("rcx") _,
                lateout("r11") _,
                options(nostack, preserves_flags),
            );
        }
        result
    }

    fn name(&self) -> &'static str {
        "getppid()"
    }
}

/// The probe installed on every service in this binary.
static NULL_SYSCALL_PROBE: Getppid = Getppid;

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

    /// Working set size in bytes for the memory benchmarks (0 = default).
    #[arg(long, default_value = "0")]
    working_set_size: u64,

    /// Output format (standalone mode only).
    #[arg(long, value_enum, default_value = "human")]
    output: OutputFormat,

    /// Emit a CSV header line before the result row.
    #[arg(long, default_value = "false")]
    csv_header: bool,

    /// Seed for deterministic benchmark data.
    ///
    /// Defaults to the same fixed constant used by `oak_cli`. This used to
    /// default to the wall clock, which meant the baseline and the enclave
    /// silently ran over different input data.
    #[arg(long, default_value_t = DEFAULT_BENCHMARK_SEED)]
    seed: u64,

    /// Number of times to repeat the whole measurement.
    ///
    /// Above one, the report becomes a median with quartiles and a stated
    /// sample count instead of a single number, and every sample is listed.
    /// A single run of a microbenchmark is one draw from a right-skewed
    /// distribution, not a measurement.
    ///
    /// Repetitions share one process, so the heap and the caches are warm from
    /// the second onwards. For the allocator and page-fault benchmarks that is
    /// a real difference rather than noise, which is why the individual
    /// samples are printed rather than only their median.
    #[arg(long, default_value = "1")]
    repetitions: u32,
}

// ── gRPC server implementation ──

mod grpc_server {
    use std::sync::Mutex;

    use benchmark::{BenchmarkService, NativeTimer, NullSyscall};
    use oak_benchmark_grpc::oak::benchmark::benchmark_server::Benchmark;
    use oak_benchmark_proto_rust::oak::benchmark::{RunBenchmarkRequest, RunBenchmarkResponse};
    use tonic::{Request, Response, Status};

    pub struct BenchmarkGrpcService {
        service: Mutex<BenchmarkService<NativeTimer>>,
    }

    impl BenchmarkGrpcService {
        pub fn new(seed: u64, probe: &'static dyn NullSyscall) -> Self {
            Self { service: Mutex::new(BenchmarkService::new(seed).with_null_syscall(probe)) }
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
                .map_err(|e| Status::internal(format!("acquiring service lock: {}", e)))?
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
        run_standalone(&args)
    }
}

async fn run_server(port: u16, seed: u64) -> Result<(), Box<dyn std::error::Error>> {
    use oak_benchmark_grpc::oak::benchmark::benchmark_server::BenchmarkServer;

    let addr = format!("0.0.0.0:{}", port).parse()?;
    let service = grpc_server::BenchmarkGrpcService::new(seed, &NULL_SYSCALL_PROBE);

    eprintln!("benchmark gRPC server listening on {}", addr);

    tonic::transport::Server::builder()
        .add_service(BenchmarkServer::new(service))
        .serve(addr)
        .await?;

    Ok(())
}

/// Run the benchmark locally and print results.
fn run_standalone(args: &Args) -> Result<(), Box<dyn std::error::Error>> {
    if args.repetitions == 0 {
        return Err("--repetitions must be at least 1".into());
    }

    let mut service =
        BenchmarkService::<NativeTimer>::new(args.seed).with_null_syscall(&NULL_SYSCALL_PROBE);

    let bytes = byte_semantics(args.benchmark);
    let mut repetitions = Vec::with_capacity(args.repetitions as usize);
    let mut last = None;

    for _ in 0..args.repetitions {
        let request = RunBenchmarkRequest {
            benchmark_type: args.benchmark as i32,
            data_size: args.data_size,
            iterations: args.iterations,
            warmup_iterations: args.warmup_iterations,
            seed: Some(args.seed),
            working_set_size: args.working_set_size,
        };

        let response = service.handle_request(request);

        // A failed benchmark returns an all-zero response. Report the error
        // rather than formatting the zeros as if they were a measurement.
        check_status(response.status)?;

        repetitions.push(Repetition {
            elapsed_tsc: response.elapsed_tsc,
            checksum: response.checksum,
            metrics: BenchmarkMetrics::calculate(
                response.elapsed_tsc,
                response.elapsed_ns,
                response.iterations_completed,
                response.bytes_processed,
                // Not needed: the native runner has a real clock and reports
                // `elapsed_ns` directly, which takes precedence over TSC
                // conversion.
                0,
                bytes,
            ),
        });
        last = Some(response);
    }

    // `last` is populated because the loop ran at least once.
    let response = last.expect("at least one repetition");

    let result = BenchmarkResult {
        benchmark_name: DisplayBenchmarkType(args.benchmark).to_string(),
        data_size: args.data_size,
        iterations_completed: response.iterations_completed,
        elapsed_tsc: response.elapsed_tsc,
        elapsed_ns: response.elapsed_ns,
        bytes_processed: response.bytes_processed,
        status: response.status,
        bytes,
        working_set_size: response.working_set_size,
        checksum: response.checksum,
        cpu_features: response.cpu_features,
        detail: sanitize_detail(&response.detail),
        // As above: the native runner has a real clock, so no TSC frequency is
        // ever applied.
        tsc_freq: TscFreq::Unused,
    };

    if args.repetitions == 1 {
        if args.csv_header && matches!(args.output, OutputFormat::Csv) {
            print!("{}", csv_header());
        }
        print!("{}", format_result(&result, &repetitions[0].metrics, args.output));
    } else {
        if args.csv_header && matches!(args.output, OutputFormat::Csv) {
            print!("{}", repeated_csv_header());
        }
        let run = RepeatedRun { result, repetitions };
        print!("{}", format_repeated(&run, args.output));
    }

    if matches!(args.output, OutputFormat::Human) {
        println!("Native CPU features: {}", CpuFeatures::from_wire(response.cpu_features));
    }

    Ok(())
}
