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
just stage0_bin oak_restricted_kernel_wrapper oak_orchestrator && \

# After building dependencies, an enclave app may be run like so:
RUST_LOG=DEBUG \
cargo run --package=oak_restricted_kernel_launcher -- \
--kernel=oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_wrapper_bin \
--vmm-binary=$(which qemu-system-x86_64) \
--memory-size=8G \
--bios-binary=stage0_bin/target/x86_64-unknown-none/release/stage0_bin \
--initrd=enclave_apps/target/x86_64-unknown-none/release/oak_orchestrator \
--app-binary=enclave_apps/target/x86_64-unknown-none/release/oak_echo_raw_enclave_app
```
