# Kernel Measurement Prediction Tool

When booting a VM the kernel and its associated setup data is measured by the
Stage 0 firmware. The VMM accepts a single bzImage format kernel file. It then
splits it into two parts, the kernel image and the kernel setup data. The VMM
also makes modifications to the setup data before passing it to Stage 0 via the
fw_cfg device.

Stage 0 measures these split, modified components rather than the original
bzImage kernel. This tool can be used to predict the Stage 0 measurements of
these components from a bzImage kernel.

The tool can be run using:

```bash
cargo run --package=oak_kernel_measurement -- \
    --kernel=oak_containers_kernel/target/bzImage
cargo run --package=oak_kernel_measurement -- \
    --kernel=oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_simple_io_init_rd_wrapper_bin
```

or by:

```bash
bazel run //oak_kernel_measurement -- \
    --kernel=$(pwd)/oak_containers_kernel/target/bzImage
bazel run //oak_kernel_measurement -- \
    --kernel=$(pwd)/oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_simple_io_init_rd_wrapper_bin
```
