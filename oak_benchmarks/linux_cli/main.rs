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
    BenchmarkMetrics, BenchmarkResult, CpuFeatures, DEFAULT_BENCHMARK_SEED, DisplayBenchmarkType,
    OutputFormat, RepeatedRun, Repetition, byte_semantics, check_status, csv_header,
    format_repeated, format_result, parse_benchmark_type, repeated_csv_header, sanitize_detail,
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

    /// Number of vCPUs for the VM.
    ///
    /// Defaults to one, matching the restricted kernel, which is
    /// single-vCPU and cannot be given more. A VM with more vCPUs can run
    /// its background services alongside the benchmark instead of competing
    /// with it, so the counts have to match for the comparison to hold.
    #[arg(long, default_value = "1")]
    vm_cpus: u8,

    /// Enable AMD SEV-SNP for the VM.
    #[arg(long)]
    enable_snp: bool,

    /// Timeout for VM boot in seconds.
    #[arg(long, default_value = "60")]
    boot_timeout: u64,

    /// How long to wait between readiness probes, in milliseconds.
    ///
    /// Together with `--probe-timeout-ms` this sets the resolution of any boot
    /// measurement: a probe every second cannot resolve a boot that takes two.
    #[arg(long, default_value = "5")]
    poll_interval_ms: u64,

    /// How long a single readiness probe may block, in milliseconds.
    ///
    /// Without a bound the loop stops being a poll. QEMU's user-mode
    /// networking binds the forwarded host port long before the guest is
    /// listening, so a probe after that point is not refused: it is accepted
    /// and held until the guest answers.
    ///
    /// This bounds the probe only. The benchmark itself runs afterwards and is
    /// not bounded by anything here.
    ///
    /// It does not by itself bound the error in a boot measurement. A probe
    /// still in flight when the guest starts answering returns immediately, so
    /// in practice the overshoot is one poll interval plus the probe's own
    /// duration, which is why that duration is reported as `probe_ns`. A probe
    /// that starts before the guest answers and times out anyway costs a
    /// further interval each time it happens.
    #[arg(long, default_value = "100")]
    probe_timeout_ms: u64,

    /// Report how long the VM took to become usable.
    ///
    /// Prints one extra line in the same shape as the enclave runner's:
    /// `boot-latency ready_ns=<n> launch_ns=<n> probe_ns=<n> attempts=<n>`.
    /// The line has its own format and is ignored by anything parsing the CSV
    /// row.
    ///
    /// `ready_ns` is the comparable figure: the clock starts immediately
    /// before the VMM is spawned and stops when the readiness probe is
    /// answered. The probe is a `debug` request, so the figure does not
    /// contain the benchmark this invocation went on to run.
    ///
    /// `launch_ns` is how long the host-side launcher took before it could
    /// start probing. It means something different on each platform and is
    /// not comparable across them. Here it is a `spawn` of a shell script
    /// that goes on to exec QEMU, so it is not even the whole of the launch.
    ///
    /// `probe_ns` is how long the successful probe took, and `attempts` how
    /// many probes there were.
    #[arg(long, default_value = "false")]
    report_boot_latency: bool,

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
    /// Must match the value used for the enclave run, otherwise the two are
    /// not processing the same data.
    #[arg(long, default_value_t = DEFAULT_BENCHMARK_SEED)]
    seed: u64,

    /// Working set size in bytes for the memory benchmarks (0 = guest default).
    #[arg(long, default_value = "0")]
    working_set_size: u64,

    /// Emit a CSV header line before the result row.
    #[arg(long, default_value = "false")]
    csv_header: bool,

    /// Output format.
    #[arg(long, value_enum, default_value = "human")]
    output: OutputFormat,

    /// Don't shut down the VM after running (for debugging).
    #[arg(long)]
    keep_vm: bool,

    /// Number of times to repeat the whole measurement.
    ///
    /// Above one, the report becomes a median with quartiles and a stated
    /// sample count instead of a single number, and every sample is listed.
    /// A single run of a microbenchmark is one draw from a right-skewed
    /// distribution, not a measurement.
    ///
    /// The VM is booted once and every repetition is a separate RPC against
    /// it, so only the first repetition sees a cold guest. The samples are
    /// printed individually because for the allocator and page-fault
    /// benchmarks that difference is the effect under study.
    #[arg(long, default_value = "1")]
    repetitions: u32,
}

/// Waits for the benchmark server to answer, and returns the client that
/// reached it.
///
/// The probe is a request of its own rather than the caller's, and a trivial
/// one, because a probe has to be bounded to stay a poll and the caller's
/// request has no bound on how long it may legitimately take. Probing with a
/// real workload would cancel and retry every benchmark whose first call
/// outlasts `probe_timeout`.
///
/// Returns the connected client, how long the probe that finally succeeded
/// took, and how many probes it took.
async fn connect(
    vm: &mut LinuxVm,
    addr: &str,
    seed: u64,
    timeout: Duration,
    poll_interval: Duration,
    probe_timeout: Duration,
) -> Result<(BenchmarkClient<Channel>, Duration, u32)> {
    // Does nothing in the guest beyond proving the server is answering; see
    // `BenchmarkType::Debug` in benchmark/service.rs.
    let request = RunBenchmarkRequest {
        benchmark_type: BenchmarkType::Debug as i32,
        data_size: 0,
        iterations: 1,
        warmup_iterations: 0,
        seed: Some(seed),
        working_set_size: 0,
    };

    let start = Instant::now();
    let mut last_error = None;
    let mut attempts = 0u32;

    loop {
        if start.elapsed() > timeout {
            return Err(last_error
                .unwrap_or_else(|| anyhow!("no readiness probe was attempted"))
                .context("waiting for the benchmark server"));
        }

        let attempt_start = Instant::now();
        attempts += 1;

        // The timeout covers the RPC as well as the connect, because it is the
        // RPC that hangs: the connect succeeds against SLIRP's bound port.
        let probe = tokio::time::timeout(probe_timeout, async {
            let channel = Channel::from_shared(format!("http://{}", addr))
                .context("parsing the server address")?
                .connect_timeout(probe_timeout)
                .connect()
                .await
                .context("connecting")?;
            let mut client = BenchmarkClient::new(channel);
            client.run_benchmark(request).await.context("probing with a debug request")?;
            Ok::<_, anyhow::Error>(client)
        })
        .await;

        match probe {
            Ok(Ok(client)) => {
                return Ok((client, attempt_start.elapsed(), attempts));
            }
            Ok(Err(e)) => {
                log::debug!("probe {attempts} failed after {:?}: {e:#}", attempt_start.elapsed());
                last_error = Some(e);
            }
            Err(_) => {
                log::debug!("probe {attempts} timed out after {:?}", attempt_start.elapsed());
                last_error = Some(anyhow!("readiness probe timed out"));
            }
        }

        // A VMM that failed to start refuses every probe, which is what a guest
        // that has not finished booting also does. Distinguishing them here
        // turns a minute of polling into an immediate, accurate error.
        if let Some(status) = vm.exited()? {
            return Err(anyhow!("the VM exited before becoming reachable: {status}"));
        }

        tokio::time::sleep(poll_interval).await;
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    env_logger::init();
    let args = Args::parse();

    // Checked before booting so a typo does not cost a VM boot, and so the
    // indexing into `repetitions` below always has something to index.
    if args.repetitions == 0 {
        return Err(anyhow!("--repetitions must be at least 1"));
    }

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
        cpus: args.vm_cpus,
        enable_snp: args.enable_snp,
    };
    // The clock for the boot measurement starts here, before the VMM exists,
    // so that everything the host does to bring the guest up is inside it.
    let launch_start = Instant::now();
    let mut vm = LinuxVm::boot(&vm_config)?;
    let launch_elapsed = launch_start.elapsed();

    eprintln!("Waiting for benchmark server on port {}...", args.port);

    // Run the benchmark.
    let request = RunBenchmarkRequest {
        benchmark_type: args.benchmark as i32,
        data_size: args.data_size,
        iterations: args.iterations,
        warmup_iterations: args.warmup_iterations,
        seed: Some(args.seed),
        working_set_size: args.working_set_size,
    };
    let addr = format!("127.0.0.1:{}", args.port);
    let timeout = Duration::from_secs(args.boot_timeout);

    let (mut client, probe_elapsed, attempts) = connect(
        &mut vm,
        &addr,
        args.seed,
        timeout,
        Duration::from_millis(args.poll_interval_ms),
        Duration::from_millis(args.probe_timeout_ms),
    )
    .await?;
    let ready_elapsed = launch_start.elapsed();

    // Printed before the benchmark runs, because the boot measurement is
    // complete at this point and does not depend on the benchmark succeeding.
    //
    // `probe_ns` is how long the probe that finally succeeded took. It bounds
    // the error in `ready_ns`: the guest became reachable at most that long
    // before the probe returned, and at most one poll interval before the
    // probe started.
    if args.report_boot_latency {
        println!(
            "boot-latency ready_ns={} launch_ns={} probe_ns={} attempts={}",
            ready_elapsed.as_nanos(),
            launch_elapsed.as_nanos(),
            probe_elapsed.as_nanos(),
            attempts
        );
    }

    // The Linux runner reports elapsed_ns directly, so the TSC frequency is
    // never needed to convert; 0 is passed as the unused fallback.
    let bytes = byte_semantics(args.benchmark);
    let mut repetitions = Vec::with_capacity(args.repetitions as usize);
    // Set on every repetition; the reported row describes the last one.
    let mut response = RunBenchmarkResponse::default();
    // Spans every repetition, so that this is the quantity `oak_cli` reports
    // under the same name. Timing one repetition would make the two runners
    // print different things. The readiness probe is already outside it.
    let host_start = Instant::now();

    for _ in 0..args.repetitions {
        // Deliberately not bounded by `--probe-timeout-ms`: that bound exists
        // to keep the readiness loop a poll, and a benchmark may take as long
        // as it takes.
        response =
            client.run_benchmark(request).await.context("running the benchmark")?.into_inner();

        // Abort before formatting: a failed benchmark returns an all-zero
        // response, which would otherwise print as a plausible row of zeros.
        // Shut the VM down first so we do not leak a QEMU process.
        if let Err(message) = check_status(response.status) {
            if !args.keep_vm {
                vm.shutdown().context("shutting down VM after a failed benchmark")?;
            }
            return Err(anyhow!(message));
        }

        repetitions.push(Repetition {
            elapsed_tsc: response.elapsed_tsc,
            checksum: response.checksum,
            metrics: BenchmarkMetrics::calculate(
                response.elapsed_tsc,
                response.elapsed_ns,
                response.iterations_completed,
                response.bytes_processed,
                0,
                bytes,
            ),
        });
    }
    let host_elapsed = host_start.elapsed();

    let result = BenchmarkResult {
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
        println!("Guest CPU features: {}", CpuFeatures::from_wire(response.cpu_features));
        println!("Host timing (wall clock, includes VM RPC round trip):");
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
