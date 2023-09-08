# This file is conceptually similar to a Makefile, but uses the `just` tool, which has a more reasonable syntax.
#
# See:
#
# - https://github.com/casey/just
# - https://just.systems/man/en/

key_xor_test_app: (build_enclave_app "key_xor_test_app")
oak_echo_enclave_app: (build_enclave_app "oak_echo_enclave_app")
oak_echo_raw_enclave_app: (build_enclave_app "oak_echo_raw_enclave_app")
oak_functions_enclave_app: (build_enclave_app "oak_functions_enclave_app")
oak_tensorflow_enclave_app: (build_enclave_app "oak_tensorflow_enclave_app")
quirk_echo_enclave_app: (build_enclave_app "quirk_echo_enclave_app")

all_enclave_apps: key_xor_test_app oak_echo_enclave_app oak_echo_raw_enclave_app oak_functions_enclave_app oak_functions_insecure_enclave_app oak_tensorflow_enclave_app quirk_echo_enclave_app

# Build a single enclave app, given its name.
build_enclave_app name:
    env --chdir=enclave_apps/$(name) cargo build --release

oak_functions_insecure_enclave_app:
    env --chdir=enclave_apps/oak_functions_enclave_app cargo build --release --no-default-features --features=allow_sensitive_logging

oak_restricted_kernel_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --bin=oak_restricted_kernel_bin

oak_restricted_kernel_simple_io_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --no-default-features --features=simple_io_channel --bin=oak_restricted_kernel_simple_io_bin

oak_restricted_kernel_wrapper: oak_restricted_kernel_bin
    env --chdir=oak_restricted_kernel_wrapper cargo build --release

stage0_bin:
    env --chdir=stage0_bin cargo objcopy --release -- --output-target=binary target/x86_64-unknown-none/release/stage0_bin

stage1_cpio:
    env --chdir=oak_containers_stage1 make

oak_containers_kernel:
    env --chdir=oak_containers_kernel make

oak_containers_system_image:
    env --chdir=oak_containers_system_image DOCKER_BUILDKIT=0 bash build.sh

oak_containers_hello_world_container_bundle_tar:
    env --chdir=oak_containers_hello_world_container DOCKER_BUILDKIT=0 bash build_container_bundle

oak_containers_hello_world_untrusted_app:
    env cargo build --release --package='oak_containers_hello_world_untrusted_app'

all_oak_containers_binaries: stage0_bin stage1_cpio oak_containers_kernel oak_containers_system_image oak_containers_hello_world_container_bundle_tar oak_containers_hello_world_untrusted_app

# Entry points for Kokoro CI.

kokoro_build_binaries_rust: all_enclave_apps oak_restricted_kernel_bin oak_restricted_kernel_simple_io_bin stage0_bin

kokoro_oak_containers: all_oak_containers_binaries
    cargo nextest run --all-targets --hide-progress-bar --package='oak_containers_hello_world_untrusted_app'

kokoro_run_tests:
    cargo nextest run --all-targets --hide-progress-bar --workspace --exclude='oak_containers_hello_world_untrusted_app'
