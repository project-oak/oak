# Oak Benchmark CLI

Host-side binary that launches the Oak benchmark enclave app, sends benchmark
commands via micro_rpc, and collects results.

## Building

```bash
bazel build -c opt //oak_benchmarks/oak_cli
```

## Running

```bash
bazel run -c opt //oak_benchmarks/oak_cli -- \
  --vmm-binary=<path-to-qemu> \
  --kernel=<path-to-oak-kernel> \
  --bios-binary=<path-to-stage0> \
  --initrd=<path-to-enclave-app> \
  --benchmark=debug \
  --iterations=100 \
  --output=human
```

See `--help` for all options.
