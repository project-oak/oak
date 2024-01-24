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

Stage0, the restricted kernel, and an enclave app may be built like so:

```shell
just stage0_bin oak_restricted_kernel_bin oak_echo_raw_enclave_app
```

After building dependencies, an enclave app may be run like so:

```shell
RUST_LOG=DEBUG \
cargo run --package=oak_restricted_kernel_launcher -- \
--enclave-binary=oak_restricted_kernel_bin/target/x86_64-unknown-none/debug/oak_restricted_kernel_bin \
--vmm-binary=$(which qemu-system-x86_64) \
--memory-size=256M \
--bios-binary=stage0_bin/target/x86_64-unknown-none/release/oak_stage0.bin \
--app-binary=enclave_apps/target/x86_64-unknown-none/debug/oak_echo_raw_enclave_app
```
