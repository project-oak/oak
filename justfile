# This file is conceptually similar to a Makefile, but uses the `just` tool, which has a more reasonable syntax.
#
# See:
#
# - https://github.com/casey/just 
# - https://just.systems/man/en/

oak_echo_enclave_app: (build_enclave_app "oak_echo_enclave_app")
oak_echo_raw_enclave_app: (build_enclave_app "oak_echo_raw_enclave_app")
oak_functions_enclave_app: (build_enclave_app "oak_functions_enclave_app")
oak_tensorflow_enclave_app: (build_enclave_app "oak_tensorflow_enclave_app")
quirk_echo_enclave_app: (build_enclave_app "quirk_echo_enclave_app")

all_enclave_apps: oak_echo_enclave_app oak_echo_raw_enclave_app oak_functions_enclave_app oak_tensorflow_enclave_app quirk_echo_enclave_app

# Build a single enclave app, given its name.
build_enclave_app name:
    env --chdir=enclave_apps/$(name) cargo build --release

oak_restricted_kernel_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release

oak_restricted_kernel_simple_io_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --no-default-features --features=simple_io_channel

stage0_bin:
    env --chdir=stage0_bin cargo objcopy --release -- --output-target=binary target/x86_64-unknown-none/release/stage0_bin

stage1_cpio:
    env --chdir=oak_containers_stage1 make

# Top level target to build all enclave apps and the kernel, and run tests.
#
# This is the entry point for Kokoro CI.
kokoro: all_enclave_apps oak_restricted_kernel_bin stage0_bin
    cargo nextest run --all-targets --hide-progress-bar

kokoro_oak_containers: stage1_cpio
