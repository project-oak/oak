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

## Architecture

```text
oak_benchmarks/
├── proto/              # Protocol definitions (micro_rpc service)
├── benchmark/          # Shared benchmark logic (no_std compatible)
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
   enclave and Linux app use the same code, ensuring apples-to-apples comparison.

3. **micro_rpc Protocol**: Communication uses the `Benchmark` service defined in
   `proto/benchmark.proto`. This provides type-safe, proto-based messaging.

4. **BenchmarkTimer Trait**: Timing is injected by the host application:
   - **Oak enclave**: `TscTimer` (TSC-based, no_std compatible)
   - **Linux**: `NativeTimer` (`std::time::Instant`-based)

   This ensures warmup iterations are correctly excluded from measurement.

## Benchmarks

### CPU-Bound: Cryptographic Hashing

Measures throughput of cryptographic hash operations with configurable data
sizes and iterations.

| Algorithm | Description             |
|-----------|-------------------------|
| SHA-256   | Standard SHA-2, 256-bit |
| SHA-512   | Standard SHA-2, 512-bit |
| SHA3-256  | Keccak-based, 256-bit   |
| SHA3-512  | Keccak-based, 512-bit   |

### Memory-Bound

| Benchmark     | What it measures                                               |
|---------------|----------------------------------------------------------------|
| Array Update  | Random writes to 256MB buffer — raw memory access latency      |
| Memory Insert | HashMap insert (key + alloc value) — allocator + hashing       |
| Memory Lookup | HashMap lookup (read-only) — hash + memory-read, no allocation |
| Alloc Churn   | Alloc/dealloc 4KB vectors — pure allocator throughput          |

## Building

> ⚠️ **IMPORTANT**: Always use `-c opt` for benchmarks! Fastbuild (default) is
> 10-100x slower due to missing optimizations and AVX instructions.

```bash
# Build all benchmark binaries (host-side)
bazel build -c opt //oak_benchmarks/...

# Build Oak kernel components (needed for Oak Enclave benchmarks).
# These target a different platform, so build together in one command
# to avoid bazel-bin symlink invalidation:
bazel build -c opt \
    //oak_benchmarks/oak_enclave_app \
    //oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin \
    //stage0_bin
```

For Linux VM benchmarks, you also need a prepared VM image — see
[`linux_vm/README.md`](linux_vm/README.md).

## Running Benchmarks

### Linux Baseline (Standalone Mode)

```bash
bazel-bin/oak_benchmarks/linux_enclave_app/linux_enclave_app \
    --benchmark=sha256 \
    --data-size=1024 \
    --iterations=10000 \
    --warmup-iterations=1000
```

Available benchmarks: `sha256`, `sha512`, `sha3-256`, `sha3-512`,
`array-update`, `memory-insert`, `memory-lookup`, `alloc-churn`, `debug`.

### Linux VM (via `linux_cli`)

`linux_cli` boots a Debian VM, waits for the benchmark server, runs the
benchmark via gRPC, and shuts down the VM — all in one command:

```bash
bazel-bin/oak_benchmarks/linux_cli/linux_cli \
    --vm-image=/tmp/benchmark-vm.qcow2 \
    --run-vm-script=oak_benchmarks/linux_vm/run_vm.sh \
    --benchmark=sha256 \
    --data-size=1024 \
    --iterations=10000
```

Use `--enable-snp` for SEV-SNP measurements. See
[`linux_vm/README.md`](linux_vm/README.md) for preparing the VM image.

### Oak Enclave

> [!NOTE]
> The enclave app is cross-compiled to a different platform. Use
> `bazel cquery --output=files` to resolve its output path.

```bash
bazel-bin/oak_benchmarks/oak_cli/oak_cli \
    --vmm-binary=$(which qemu-system-x86_64) \
    --kernel=bazel-bin/oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper_virtio_console_channel_bin \
    --bios-binary=bazel-bin/stage0_bin/stage0_bin \
    --initrd=$(bazel cquery --output=files -c opt //oak_benchmarks/oak_enclave_app 2>/dev/null) \
    --memory-size=512M \
    --benchmark=sha256 \
    --data-size=1024 \
    --iterations=10000
```

## Notes

> [!IMPORTANT]
> **Warmup Iterations**: Use `--warmup-iterations` (default: 1000)
> to warm the CPU's branch predictor and caches before measurement. Without
> warmup, the first ~1000 iterations can be 20-40% slower due to cold code
> paths.

<!-- -->

> [!IMPORTANT]
> **TSC Frequency**: The benchmarks assume a fixed TSC frequency
> (default 3.0 GHz). Adjust with `--tsc-freq` for your hardware. Check:
> `dmesg | grep -i tsc`

<!-- -->

> [!IMPORTANT]
> For accurate paper evaluation, the Linux baseline **must be run
> inside an SEV-SNP VM** to include memory encryption overhead. Running
> natively on the host gives an unfair advantage.

## Preparing a Linux VM

See [`linux_vm/README.md`](linux_vm/README.md) for instructions on downloading
a Debian base image, installing the benchmark binary, and running benchmarks
inside a VM.
