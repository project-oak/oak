# Oak Benchmark Enclave App

This is the enclave application that runs inside the Oak Restricted Kernel and
executes microbenchmarks.

## Overview

The enclave app is a single binary that hosts all microbenchmarks. It:

1. Waits for commands from the host via micro_rpc
2. Executes the requested benchmark
3. Returns timing results (TSC ticks and nanoseconds)

## Supported Benchmarks

| Type         | Status         | Description                             |
| ------------ | -------------- | --------------------------------------- |
| Debug        | ✅ Implemented | Connectivity test (no real computation) |
| SHA256       | 🔲 Planned     | CPU-heavy hashing benchmark             |
| P256Sign     | 🔲 Planned     | ECDSA signing benchmark                 |
| MemoryInsert | 🔲 Planned     | HashMap insertion stress test           |
| MemoryLookup | 🔲 Planned     | HashMap lookup performance              |
| ArrayUpdate  | 🔲 Planned     | Array write performance                 |

## Building

```bash
bazel build -c opt //oak_benchmarks/oak_enclave_app
```

## Notes

- Random data is generated at startup from a fixed seed, the same one the Linux
  baseline uses, so both operate on identical data
- Data buffer is pre-allocated to avoid allocation during benchmarks
- Each benchmark iteration is measured on the guest side using RDTSCP
