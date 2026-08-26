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
    RepeatedRun, Repetition, byte_semantics, check_status, csv_header, detect_tsc_freq,
    format_repeated, format_result, parse_benchmark_type, repeated_csv_header, sanitize_detail,
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

    /// Report how long the enclave took to become usable.
    ///
    /// Prints one extra line in the same shape as the Linux runner's:
    /// `boot-latency ready_ns=<n> launch_ns=<n> probe_ns=<n> attempts=<n>`.
    /// The line has its own format and is ignored by anything parsing the CSV
    /// row.
    ///
    /// `ready_ns` is the comparable figure: the clock starts immediately
    /// before the VMM is spawned and stops when the first RPC response
    /// arrives. It contains the benchmark itself, so use one that does no
    /// work: `--benchmark=debug --iterations=1`.
    ///
    /// `launch_ns` is how long the host-side launcher took before it could
    /// send anything. It means something different on each platform and is
    /// not comparable across them.
    ///
    /// `probe_ns` and `attempts` are always zero here, because this platform
    /// has no readiness loop: the launcher creates a socket pair rather than
    /// binding a port that has to be polled.
    #[arg(long, default_value = "false")]
    report_boot_latency: bool,

    /// Number of times to repeat the whole measurement.
    ///
    /// Above one, the report becomes a median with quartiles and a stated
    /// sample count instead of a single number, and every sample is listed.
    /// A single run of a microbenchmark is one draw from a right-skewed
    /// distribution, not a measurement.
    ///
    /// The enclave is launched once and every repetition is a separate RPC
    /// against it, so only the first repetition sees a cold heap. The samples
    /// are printed individually because for the allocator and page-fault
    /// benchmarks that difference is the effect under study.
    #[arg(long, default_value = "1")]
    repetitions: u32,
}

#[tokio::main]
async fn main() -> Result<()> {
    let args = Args::parse();
    env_logger::init();

    // Checked before launching so a typo does not cost an enclave boot, and so
    // that the "at least one repetition" expectation below cannot fire.
    if args.repetitions == 0 {
        anyhow::bail!("--repetitions must be at least 1");
    }

    log::info!("Starting Oak Benchmark Host Runner");
    log::info!("Benchmark: {:?}", args.benchmark);
    log::info!("Data size: {} bytes", args.data_size);
    log::info!("Iterations: {}", args.iterations);

    // Detected before the launch clock starts: calibration spins for 50 ms,
    // and that is host-side setup rather than any part of the guest coming up.
    // Measuring it inside the boot window would have added the whole 50 ms to
    // every reported boot latency. It is detected once because the frequency
    // does not change between repetitions.
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
                 be scaled incorrectly, prefer the TSC ticks/op column",
                detected.source_description()
            );
        }
        detected.hz()
    });

    // Launch the enclave.
    log::info!("Launching enclave...");
    let launch_start = Instant::now();
    let (guest_instance, connector_handle) = launcher::launch(args.launcher_params)
        .await
        .map_err(|e| anyhow::anyhow!("launching the enclave: {e}"))?;
    let launch_elapsed = launch_start.elapsed();

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

    let bytes = byte_semantics(args.benchmark);

    // The boot measurement stops here, on a request of its own, so that it does
    // not contain the benchmark this invocation goes on to run. The Linux
    // runner bounds and repeats the equivalent request as a readiness probe;
    // this one needs neither, because the launcher hands back an established
    // channel rather than a port that has to be polled. What matters is that
    // both platforms stop the clock on the same trivial request, which is an
    // invariant of the two runners rather than something the caller has to
    // arrange by passing `--benchmark=debug`.
    if args.report_boot_latency {
        let probe = RunBenchmarkRequest {
            benchmark_type: BenchmarkType::Debug as i32,
            data_size: 0,
            iterations: 1,
            warmup_iterations: 0,
            seed: Some(args.seed),
            working_set_size: 0,
        };
        client
            .run_benchmark(&probe)
            .await
            .map_err(|e| anyhow::anyhow!("invoking the readiness probe: {e:?}"))?
            .map_err(|e| anyhow::anyhow!("readiness probe returned an error: {e:?}"))?;

        // `probe_ns` and `attempts` are zero rather than one: this platform has
        // no readiness loop to describe, so there is no probe duration that
        // could bound the error in `ready_ns`.
        println!(
            "boot-latency ready_ns={} launch_ns={} probe_ns=0 attempts=0",
            launch_start.elapsed().as_nanos(),
            launch_elapsed.as_nanos(),
        );
    }

    let host_start = Instant::now();
    let mut repetitions = Vec::with_capacity(args.repetitions as usize);
    let mut last = None;

    for _ in 0..args.repetitions {
        // Call the RunBenchmark RPC.
        let response = client
            .run_benchmark(&request)
            .await
            .map_err(|e| anyhow::anyhow!("invoking the benchmark RPC: {e:?}"))?
            .map_err(|e| anyhow::anyhow!("benchmark RPC returned an error: {e:?}"))?;

        // Abort before formatting: a failed benchmark returns an all-zero
        // response, which would otherwise be printed as a plausible-looking
        // row of zeros. Tear the enclave down first so we do not leak a QEMU
        // process.
        if let Err(message) = check_status(response.status) {
            guest_instance.kill().await.context("terminating enclave after a failed benchmark")?;
            anyhow::bail!(message);
        }

        repetitions.push(Repetition {
            elapsed_tsc: response.elapsed_tsc,
            checksum: response.checksum,
            metrics: BenchmarkMetrics::calculate(
                response.elapsed_tsc,
                response.elapsed_ns,
                response.iterations_completed,
                response.bytes_processed,
                tsc_freq,
                bytes,
            ),
        });
        last = Some(response);
    }

    let host_elapsed = host_start.elapsed();
    // Populated because `repetitions` is validated to be at least one.
    let response = last.expect("at least one repetition");

    log::info!("guest CPU features: {}", CpuFeatures::from_wire(response.cpu_features));

    // Output results using cli_common formatter.
    let result = cli_common::BenchmarkResult {
        benchmark_name: DisplayBenchmarkType(args.benchmark).to_string(),
        data_size: args.data_size,
        iterations_completed: response.iterations_completed,
        elapsed_tsc: response.elapsed_tsc,
        elapsed_ns: repetitions[repetitions.len() - 1].metrics.elapsed_ns,
        bytes_processed: response.bytes_processed,
        status: response.status,
        bytes,
        working_set_size: response.working_set_size,
        checksum: response.checksum,
        cpu_features: response.cpu_features,
        detail: sanitize_detail(&response.detail),
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
