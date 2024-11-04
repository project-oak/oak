# oak_restricted_kernel_launcher

Simple launcher used to launch an instance of the restricted kernel in a VM.

Documentation is available via:

```shell
cargo run --package=oak_restricted_kernel_launcher -- --help
```

The instructions below for building the required dependencies and running an app
using this launcher are provided on a best effort basis.

First the dependencies used to run launch an instance of the restricted kernel
must be built.

(instructions gained from inspecting xtask, may change in the future)

```shell
# Stage0, the restricted kernel, and an enclave app may be built like so:
just \
  stage0_bin \
  oak_restricted_kernel_wrapper_virtio_console_channel \
  build_oak_orchestrator build_oak_multi_process_test && \

# Build an enclave app like so:
just build_enclave_app build_oak_multi_process_test && \

# After building dependencies, an enclave app may be run like so:
RUST_LOG=DEBUG \
cargo run --package=oak_restricted_kernel_launcher -- \
--kernel=oak_restricted_kernel_wrapper/bin/wrapper_bzimage_virtio_console_channel \
--vmm-binary=$(which qemu-system-x86_64) \
--memory-size=8G \
--bios-binary=artifacts/stage0_bin \
--initrd=artifacts/enclave_apps/oak_orchestrator \
--app-binary=artifacts/enclave_apps/oak_multi_process_test
```
