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

## Making a Comparison Valid

Two runs are only comparable if they did the same work with the same tools.
Three mechanisms enforce this, and all three should be checked before any number
is quoted:

1. **Same input data.** `--seed` defaults to a fixed constant shared by every
   CLI (`DEFAULT_BENCHMARK_SEED`). Earlier versions derived the seed from the
   clock independently on each platform, so the two sides silently processed
   different data.
2. **Same result.** Every response carries a `checksum` over the benchmark
   output. For a given benchmark, seed and parameter set it **must** be
   identical on both platforms. A mismatch means the comparison is invalid, not
   merely noisy. `null-syscall` is the exception: the two platforms call
   different syscalls, so its checksum can only count successful returns and
   matches for free. See [Kernel Boundary](#kernel-boundary).
3. **Same instruction set.** Every response carries `cpu_features`, reporting
   the compile-time target features, the `CPUID` features, and whether the
   crypto crates can dispatch on the latter at runtime. The _effective_ sets
   should match. The field covers SHA-NI, AES-NI, PCLMULQDQ, AVX2, AVX-512 IFMA
   and AVX-512VL. It has already caught two real problems: bare-metal builds
   silently using software SHA-2 and AES, and `curve25519-dalek` selecting an
   AVX-512 IFMA backend on Linux while the enclave fell back to AVX2, worth
   1.65x on Ed25519. AES-NI and PCLMULQDQ now agree; **SHA-NI and AVX-512 IFMA
   still do not**, and the `sha256` and `ed25519-*` ratios should not be quoted
   as enclave overhead until they do. Note that this field covers only the
   dispatch-capable crypto crates, **not** general codegen: two binaries can
   report identical effective features while one was compiled for a newer
   baseline ISA than the other. The baseline's build transition below is what
   closes that gap. See [Crypto acceleration](#crypto-acceleration) below.

## Metrics

The headline metric is **TSC ticks per operation**, computed from the guest's
own TSC reading. It requires no knowledge of the TSC frequency and therefore
cannot be distorted by a mis-detected one, which makes it the safest number to
compare across platforms.

It is **not** retired core cycles, and the field is named `tsc_ticks_per_op`
rather than `cycles_per_op` to stop it claiming otherwise. The TSC is invariant:
it advances at a fixed rate no matter what frequency the core is running at, so
a tick figure is wall time in a unit that happens to need no calibration.
Retired cycles would need a performance counter, and the enclave has no access
to one. Anything comparing these numbers against a published cycle count should
know which of the two it is looking at.

Every run reports ticks per operation and **nanoseconds per operation** side by
side, following the form of Unikraft's syscall table (EuroSys 2021, Table 1),
which prints `#Cycles` and `nsecs` in adjacent columns. Ticks are the honest
cross-platform comparison; nanoseconds are what a reader can check against their
own intuition.

For the hash and AEAD benchmarks the report also carries **TSC ticks per byte**,
the unit [eBACS](https://bench.cr.yp.to/results-hash.html) publishes, always
against a stated message size. It is deliberately absent elsewhere: emitting it
for the allocator benchmark would invite a comparison the number cannot support.

`bytes_processed` does not count the same thing in every benchmark, so every
byte rate is printed with a label saying what its bytes are — message bytes for
a hash, key and value bytes for a map operation, bytes requested from the
allocator for `alloc-churn`, bytes written for `array-update`. Only figures
sharing a label are comparable with each other. The `ByteSemantics` type in
[`cli_common/cli.rs`](cli_common/cli.rs) is the single definition.

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

The authoritative list of names is `BENCHMARKS` in
[`cli_common/cli.rs`](cli_common/cli.rs); pass one of them to `--benchmark`.
That one table also carries each benchmark's display name and byte semantics, so
those cannot drift apart from the parser.

### CPU-Bound: Cryptographic Hashing

Measures throughput of cryptographic hash operations with configurable data
sizes and iterations.

| Algorithm | Description             |
| --------- | ----------------------- |
| SHA-256   | Standard SHA-2, 256-bit |
| SHA-512   | Standard SHA-2, 512-bit |
| SHA3-256  | Keccak-based, 256-bit   |
| SHA3-512  | Keccak-based, 512-bit   |

### CPU-Bound: Public-Key and AEAD Crypto

| Benchmark        | What it measures                                |
| ---------------- | ----------------------------------------------- |
| P-256 Sign       | ECDSA signing, RFC 6979 deterministic nonces    |
| P-256 Verify     | ECDSA verification over precomputed signatures  |
| Ed25519 Sign     | EdDSA signing over Curve25519                   |
| Ed25519 Verify   | EdDSA verification, strict                      |
| AES-256-GCM Seal | Authenticated encryption                        |
| AES-256-GCM Open | Authenticated decryption over cached ciphertext |

Deterministic nonces are used so that no random number generator is needed in
the enclave, and so that both platforms produce byte-identical signatures.

Ed25519 is roughly an order of magnitude cheaper than P-256 here. Two build
choices affect the absolute numbers and neither is guessable from the output:
`ed25519-dalek` is built without `precomputed-tables`, and verification uses
`verify_strict`, which additionally rejects small-order keys and `R` values.

### Memory-Bound

| Benchmark     | What it measures                                                  |
| ------------- | ----------------------------------------------------------------- |
| Array Update  | Random single-byte writes over `--working-set-size` bytes         |
| Memory Insert | HashMap insert into an unreserved map, including growth/rehash    |
| Memory Lookup | HashMap lookup (read-only) — hash plus memory read, no allocation |
| Memory Churn  | HashMap evict and insert at constant size — free then alloc       |
| Alloc Churn   | Alloc/dealloc churn — pure allocator throughput                   |
| Pointer Chase | Dependent-load latency and TLB reach — see below                  |
| Page Touch    | Cost of provisioning fresh memory — see below                     |

The three hash map modes are meant to be read together. Insert only ever grows
the heap: it covers the table's growth and rehash path, but every key lands in a
bucket that was empty and the allocator's free path is never used. Churn evicts
a resident key and inserts one that has never been in the map, holding the size
constant, so it covers the free path and the deleted-slot bookkeeping that goes
with it. Lookup allocates nothing at all.

Two caveats before reading churn as an allocator result. The value size is
fixed, so the allocator only ever sees one size class and the block it frees is
usually the one it is asked for next — its fast path, which glibc serves from a
per-thread cache without taking a lock. Size variation lives in `alloc-churn`,
not here. And the enclave allocator is `rlsf`'s TLSF behind a spinlock, so part
of any gap is the lock and the coalescing rather than allocator quality.

Churn rebuilds the map after measuring, outside the timed region, so that a
later request against the same enclave process sees the map a fresh one would. A
churn request therefore takes about twice as long as its iteration count
suggests.

Use `--working-set-size` to choose the footprint; pick values that straddle the
L3 cache so both cache-resident and DRAM-resident behaviour are covered. Alloc
churn takes its allocation size from `--data-size`, where `0` selects a rotating
schedule of size classes that exercises allocator size-class boundaries.

> [!IMPORTANT] The enclave needs a guest large enough to hold the working set.
> Pass `--memory-size` to `oak_cli` accordingly, with headroom: `pointer-chase`
> peaks at nine eighths of its working set during setup, because the permutation
> is built in a separate dense array before being scattered, and the hash map
> modes need about half as much again for the key array and the table's
> load-factor headroom. These benchmarks allocate with `try_reserve`, so an
> undersized guest reports `allocation failure` rather than aborting.

### Memory-Bound: Latency and Page Size

`pointer-chase` walks a randomly permuted list of cache lines where each access
supplies the address of the next, so nothing can be prefetched or overlapped and
`tsc_ticks_per_op` is the load-to-use latency directly. It is the construction
used by lmbench's
[`lat_mem_rd`](https://lmbench.sourceforge.net/man/lat_mem_rd.8.html), which
cannot run here because it needs `fork`, signals and a filesystem.

Sweeping `--working-set-size` across the cache hierarchy gives the usual latency
curve, directly comparable with any published `lat_mem_rd` figure.

It was also added to expose a page-size difference. Measurement did not find one
where it was expected.

The enclave heap is mapped in 2 MiB units by construction, and the expectation
was that the baseline would be on 4 KiB pages and would spend most of a
large-working-set run walking page tables. At the top of the range it does not:
`transparent_hugepage/enabled` is `always`, and sampling
`/proc/<pid>/smaps_rollup` while the baseline runs shows `AnonHugePages`
covering 100% of a 256 MiB or 1 GiB working set. Nor could the difference show
there anyway — with 2 MiB pages the 4 GiB maximum needs 2048 entries of the
reference part's 3072-entry L2 TLB, so where both platforms get 2 MiB pages
neither should walk.

Around 1 MiB there is a real band of roughly 2x, which narrows to the backing of
the allocation rather than to the platform: a Linux process that aligns its
`mmap` to 2 MiB, or asks for `MADV_HUGEPAGE`, closes it completely. Report it as
a difference in allocator defaults, not as a capability the enclave has and
Linux lacks.

What the benchmark is good for instead is a positive control on the
virtualisation wrapper. Outside that band there is no translation term and the
DRAM subsystem is the host's on both sides, so a ratio of 1.0 is a testable
prediction, and confirming it licenses attributing differences elsewhere to the
kernels rather than to QEMU. At 32 KiB both platforms are L1 resident, which
compares the emitted loops themselves and rules out codegen divergence between
the two targets.

`--iterations` is rounded up to at least one full lap of the buffer, so a short
request cannot report a working set larger than the region it visited; the count
actually used is in `iterations_completed`. There is no cold mode — the
constructor verifies the cycle by walking the whole buffer, so everything has
been touched once before measurement starts.

`page-touch` allocates a region, writes one word to each 4 KiB page of it, and
frees it, once per iteration. `--working-set-size` is the per-iteration region
size. Unlike every other benchmark here, the allocation is **inside** the timed
region, because provisioning is the thing being measured.

> [!WARNING] Several things differ between the platforms at once and this
> benchmark cannot separate them. Linux resolves a first write with a page
> fault; the Restricted Kernel maps and zeroes eagerly at `mmap` time, so a
> first write never traps. Independently, the enclave heap never returns memory
> to the kernel, while glibc unmaps chunks above its mmap threshold — dynamic,
> starting at 128 KiB and capped at 32 MiB, see
> [`mallopt(3)`](https://man7.org/linux/man-pages/man3/mallopt.3.html) — and
> re-faults them next time. The two sides also move different volumes of memory
> to do it: Linux zeroes the whole region, the enclave writes one word per page.
> Compare a cold run (`--iterations=1 --warmup-iterations=0`) against a warm one
> rather than reading either alone.

Even having done that, the warm side needs one more caveat.

> [!CAUTION] The warm ratio is a function of `--iterations`, not a property of
> the platforms. Linux re-pays provisioning every iteration while the enclave
> pays once and recycles, so with no warmup the enclave's cost is
> `touch + one_time / iterations`, falling towards `touch`. At 64 MiB and
> `--warmup-iterations=0` it looks 2.6x cheaper at 10 iterations and 26x at
> 10000, already within a percent of that ceiling. With the default warmup the
> one-time cost lands before the timer starts and the ratio is flat. Report the
> curve, or state the iteration and warmup counts beside any single figure.

The cold number is not purely the guest's either. Guest RAM is an ordinary
anonymous mapping in the QEMU process with no `-mem-prealloc`, so the host
demand-pages it. Sampling the QEMU process during a cold run shows peak RSS
rising by 66 MiB for a 64 MiB region and 262 MiB for a 256 MiB region, almost
entirely `AnonHugePages` — the host instantiates and zeroes the same memory
underneath, in 2 MiB units, inside the guest's timed region. On hardware with
preallocated private memory that component would not be present.

### Kernel Boundary

`null-syscall` measures one user/kernel round trip, the analogue of lmbench's
`lat_syscall null`.

> [!WARNING] The two platforms deliberately invoke **different syscalls**: the
> enclave uses `write(-1, NULL, 0)`, which the Restricted Kernel answers before
> looking up the descriptor, and Linux uses `getppid()`. Each is the cheapest
> crossing its kernel offers, which is what lmbench does, but it makes the
> result a comparison of kernels rather than of one syscall. The syscall that
> was actually measured is reported in the `detail` column. Any use of this
> number has to carry that caveat.

The checksum is no help here. The two syscalls return different values, so it
can only fold the count of successful returns, and the run already fails if that
count is short of the request. It matches across platforms for free.

`syscall-control` runs the same loop with no syscall in it: the loop, the
indirect call through the probe, the barrier and the timer. Subtracting a
platform's control from its own figure estimates the kernel crossing, and only
estimates it — the source is identical but the two targets are built with
different flags, and the two loops leave the branch predictor and caches in
different states. Report both numbers.

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
   - **Linux**: `NativeTimer`, which records **both** `std::time::Instant` and
     the TSC, so that cycles/op is available on both platforms

   This ensures warmup iterations are correctly excluded from measurement.

## Crypto Acceleration

The `sha2` and `aes` crates pick a hardware backend through the `cpufeatures`
crate, which does a runtime `CPUID` check. On `x86_64-unknown-none` there is no
OS to support that check, so `cpufeatures` compiles it out and the crates fall
back to whatever the _compile-time_ target features allow.

The consequence, before this was addressed, was that the enclave binary
contained zero SHA-NI and zero AES-NI instructions while the Linux baseline
contained 56 and 462 respectively. A naive comparison then reported a large
"enclave overhead" that was really the gap between a hardware and a software
implementation of the same primitive.

AES-NI is fixed. [`bazel/rust/defs.bzl`](../bazel/rust/defs.bzl) puts
`+aes,+pclmulqdq` in `ENCLAVE_TARGET_FEATURES`, and both sides now issue the
same VEX-encoded `vaesenc`. To verify:

```bash
objdump -d "$(bazel cquery -c opt --output=files \
    //oak_benchmarks/oak_enclave_app:oak_enclave_app)" |
    grep -cE 'v?aesenc'
```

### SHA-NI is deliberately absent, and SHA-256 is still asymmetric

`+sha` was enabled once and then removed. SHA-NI is missing from pre-Ice Lake
Intel parts, and a binary built with it raises an invalid-opcode fault on
machines still used for development, so `ENCLAVE_TARGET_FEATURES` carries no
`+sha`. The same census returns zero for the enclave and 56 for the baseline:

```bash
objdump -d "$(bazel cquery -c opt --output=files \
    //oak_benchmarks/oak_enclave_app:oak_enclave_app)" |
    grep -cE 'sha256rnds2|sha256msg'
```

The `matched_isa_binary` transition described below cannot close that gap. The
transition sets compile-time target features, while `sha2` reaches SHA-NI
through a runtime `CPUID` check whose body lives in a
`#[target_feature(enable = "sha")]` function, which the compiler emits whatever
the global flags say. `curve25519-dalek` selects its AVX-512 IFMA backend the
same way, which is why `ed25519-sign` and `ed25519-verify` are asymmetric too.
The baseline exports `sha2::sha256::x86::shani_cpuid::STORAGE` and
`curve25519_dalek::backend::get_selected_backend::cpuid_avx512::STORAGE`; the
enclave exports neither.

So `sha256` reports the enclave at roughly 4.7x the baseline, and `ed25519-*` at
roughly 1.7x. Those figures measure the absence of runtime CPU feature detection
under `no_std`. They are not a cost the Restricted Kernel imposes, and quoting
them as such would be wrong.

To measure the primitive rather than the dispatch, force the baseline to the
software backend. `sha2` has a `force-soft` feature, already applied to
`ONLY_NO_STD_NO_AVX` in `MODULE.bazel`; widening that scope makes SHA-256
like-for-like. The enclave-side alternative, restoring `+sha`, is what the
hardware supports here but not everywhere.

### The baseline is built to match

Correcting the enclave side exposes the same problem in the opposite direction.
The bare-metal toolchain sets `--codegen=target-cpu=x86-64-v3` and an explicit
target-feature list, but nothing sets either for `x86_64-unknown-linux-gnu`, so
the baseline is compiled for the generic x86-64 target: no AVX2, no AES-NI. Left
alone, that biases every workload the compiler can vectorise, and every one that
reaches for AES-NI, in the enclave's favour.

`//oak_benchmarks/linux_enclave_app` closes the gap itself. It is a
`matched_isa_binary`, defined in [`defs.bzl`](linux_enclave_app/defs.bzl), which
applies a configuration transition that compiles the binary and every crate it
links with the enclave's instruction set. No build flag is needed, and an
unmatched baseline cannot be produced by accident:

```bash
bazel build -c opt //oak_benchmarks/linux_enclave_app
```

The transition lists the target features explicitly rather than relying on
`target-cpu=x86-64-v3` to imply them, because the v3 level does not include
AES-NI. That distinction is load-bearing for the hash map benchmark: `ahash`
picks its backend from `cfg(target_feature = "aes")` at compile time, and with
`target-cpu=x86-64-v3` alone it still compiles the fallback backend, so the two
sides would hash differently.

`:linux_enclave_app_base` is the same binary without the transition, which is
what to build when you want to measure the gap rather than close it.

To confirm both sides agree, compare the instruction census rather than trusting
the `cpu_features` field:

```bash
objdump -d "${binary}" |
    grep -oE '\b(v?aesenc|sha256rnds2|rorx|mulx)\b' | sort | uniq -c
```

Both binaries should show `vaesenc` rather than the legacy `aesenc`, in
comparable quantity, and non-zero `rorx`/`mulx`. `sha256rnds2` is the exception:
the baseline has it and the enclave does not, for the reason given above.

## Notes

> [!IMPORTANT] **Warmup Iterations**: Use `--warmup-iterations` (default: 1000)
> to warm the CPU's branch predictor and caches before measurement. Without
> warmup, the first ~1000 iterations can be 20-40% slower due to cold code
> paths.

<!-- -->

> [!IMPORTANT] **TSC Frequency**: The host measures the TSC frequency against
> `CLOCK_MONOTONIC` at startup; `--tsc-freq` overrides it. Do not rely on the
> sysfs `cpuinfo_max_freq` value: under `amd_pstate` it reports the boost clock
> rather than the invariant TSC rate. Cross-check with
> `journalctl -k | grep -i "refined tsc"`. Prefer cycles/op, which needs no
> frequency at all.

<!-- -->

> [!WARNING] **Guest memory**: the launcher passes no `-m` to QEMU unless
> `--memory-size` is given, leaving the enclave with ~112 MiB usable. The
> benchmarks that allocate with `try_reserve` report `allocation failure`;
> `array-update` and the hash-map benchmarks use `vec![]`, which aborts the
> guest because the Oak allocator panics rather than returning an error. Pass
> `--memory-size=4G` (or more) for the memory benchmarks, and keep it constant
> across a comparison.

<!-- -->

> [!IMPORTANT] For accurate paper evaluation, the Linux baseline **must be run
> inside an SEV-SNP VM** to include memory encryption overhead. Running natively
> on the host gives an unfair advantage.
