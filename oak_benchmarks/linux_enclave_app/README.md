# Linux Baseline Benchmark Runner

Runs the same benchmark logic as the Oak enclave app, but natively on Linux.
Uses the exact same `benchmark` crate to ensure an "apples-to-apples"
comparison.

## Building

```bash
bazel build -c opt //oak_benchmarks/linux_enclave_app
```

## Running

```bash
bazel run -c opt //oak_benchmarks/linux_enclave_app -- \
  --benchmark=debug \
  --iterations=100 \
  --output=human
```
