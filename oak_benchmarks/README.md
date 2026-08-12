# Oak Benchmarks

Benchmarking infrastructure for evaluating Oak Restricted Kernel performance.

## Introduction

Project Oak provides a Trusted Execution Environment (TEE) with strong security
guarantees through hardware isolation and memory encryption. A key question for
adoption is: **what is the performance trade-off of these security guarantees?**

This suite answers that question by running identical workloads in:

- **Oak Enclave**: Application running inside Oak Restricted Kernel (with TEE
  protections)
- **Linux VM**: Same application running in a standard Debian VM (baseline)

Both environments run the exact same benchmark code (`benchmark/`) to ensure
fair comparison. The results inform the evaluation section of the Oak Paper.

## Running Benchmarks

### Oak Enclave

The enclave app is cross-compiled during the build process. A `<name>_run`
target automatically handles path resolution for the QEMU binary, restricted
kernel, stage0 BIOS, and the enclave `initrd` payload.

> ⚠️ **IMPORTANT**: Always use `-c opt` for benchmarks! Fastbuild (default) is
> 10-100x slower due to missing optimizations and AVX instructions.

```bash
bazel run -c opt //oak_benchmarks/oak_enclave_app:oak_enclave_app_run -- \
    --memory-size=512M \
    --benchmark=sha256 \
    --data-size=1024 \
    --iterations=10000
```

### Linux VM (via `linux_cli`)

`linux_cli` boots a Debian VM, waits for the benchmark server, runs the
benchmark via gRPC, and shuts down the VM — all in one command.

The `vm_disk_image` macro automatically generates a `<name>_run` target for
this:

```bash
bazel run -c opt //oak_benchmarks/linux_enclave_app:linux_enclave_image_run -- \
    --benchmark=sha256 \
    --data-size=1024 \
    --iterations=10000
```

Use `--enable-snp` for SEV-SNP measurements. See
[`linux_vm/README.md`](linux_vm/README.md) for more details on the VM image.

### Linux Baseline (Standalone Mode)

To run the benchmark natively on your host Linux machine as a standalone
process:

```bash
bazel run -c opt //oak_benchmarks/linux_enclave_app -- \
    --benchmark=sha256 \
    --data-size=1024 \
    --iterations=10000 \
    --warmup-iterations=1000
```

## Available Benchmarks

### CPU-Bound: Cryptographic Hashing

Measures throughput of cryptographic hash operations with configurable data
sizes and iterations.

| Algorithm | Description             |
| --------- | ----------------------- |
| SHA-256   | Standard SHA-2, 256-bit |
| SHA-512   | Standard SHA-2, 512-bit |
| SHA3-256  | Keccak-based, 256-bit   |
| SHA3-512  | Keccak-based, 512-bit   |

### Memory-Bound

| Benchmark     | What it measures                                                |
| ------------- | --------------------------------------------------------------- |
| Array Update  | Random writes to a caller-sized buffer — memory access latency  |
| Memory Insert | HashMap insert (key + alloc value) — allocator + hashing        |
| Memory Lookup | HashMap lookup (read-only) — hash + memory-read, no allocation  |
| Alloc Churn   | Alloc/dealloc at a fixed or cycling size — allocator throughput |

Available benchmarks: `sha256`, `sha512`, `sha3-256`, `sha3-512`,
`array-update`, `memory-insert`, `memory-lookup`, `alloc-churn`, `debug`.

## Reproducing a Comparison

A comparison between the enclave and the Linux baseline only means something if
both sides did the same work, so the parameters that decide it travel in the
request.

| Flag                 | Effect                                                        |
| -------------------- | ------------------------------------------------------------- |
| `--seed`             | Fixes the pseudo-random input; both sides need the same value |
| `--working-set-size` | Working set in bytes for the memory benchmarks (0 = default)  |
| `--csv-header`       | Emits a header row before the CSV result row                  |

Results carry a `checksum` over each benchmark's output and the `cpu_features`
the guest was built with and found at runtime. Treat a comparison as invalid
unless both sides report the same checksum, and read a difference in
`cpu_features` as the two sides having run different instruction sets rather
than as a difference between the kernels.

## Manual Building

For development, you can build the binaries directly without invoking
`bazel run`.

```bash
# Build all benchmark host CLIs
bazel build -c opt //oak_benchmarks/...

# Build Oak kernel components (needed for Oak Enclave benchmarks manually).
bazel build -c opt \
    //oak_benchmarks/oak_enclave_app \
    //oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin \
    //stage0_bin
```

## Architecture

```text
oak_benchmarks/
├── proto/              # Protocol definitions (micro_rpc service)
├── benchmark/          # Shared benchmark logic (#![no_std] compatible)
├── cli_common/         # Shared CLI parsing and result formatting
├── oak_enclave_app/    # Enclave app (runs inside Oak Restricted Kernel)
├── oak_cli/            # Host-side orchestrator for Oak VM
├── linux_enclave_app/  # Linux baseline (standalone CLI + gRPC server)
├── linux_cli/          # Host-side CLI for Linux VM (gRPC client + VM mgmt)
└── linux_vm/           # Scripts for preparing benchmark VMs
```

### Key Design Decisions

1. **Single Enclave Binary**: The `oak_enclave_app` hosts all microbenchmarks.
   The host sends a command to select which benchmark to run, avoiding cold-boot
   overhead between tests.

2. **Code Sharing**: The `benchmark` crate is `#![no_std]` compatible. Both the
   enclave and Linux app use the same code, ensuring apples-to-apples
   comparison.

3. **micro_rpc Protocol**: Communication uses the `Benchmark` service defined in
   `proto/benchmark.proto`. This provides type-safe, proto-based messaging.

4. **BenchmarkTimer Trait**: Timing is injected by the host application:
   - **Oak enclave**: `TscTimer` (TSC-based, no_std compatible)
   - **Linux**: `NativeTimer` (`std::time::Instant`-based)

   This ensures warmup iterations are correctly excluded from measurement.

## Notes

> [!IMPORTANT] **Warmup Iterations**: Use `--warmup-iterations` (default: 1000)
> to warm the CPU's branch predictor and caches before measurement. Without
> warmup, the first ~1000 iterations can be 20-40% slower due to cold code
> paths.

<!-- -->

> [!IMPORTANT] **TSC Frequency**: The benchmarks assume a fixed TSC frequency
> (default 3.0 GHz). Adjust with `--tsc-freq` for your hardware. Check:
> `dmesg | grep -i tsc`

<!-- -->

> [!IMPORTANT] For accurate paper evaluation, the Linux baseline **must be run
> inside an SEV-SNP VM** to include memory encryption overhead. Running natively
> on the host gives an unfair advantage.
