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
oak_orchestrator: (build_enclave_app "oak_orchestrator")

all_enclave_apps: key_xor_test_app oak_echo_enclave_app oak_echo_raw_enclave_app oak_functions_enclave_app oak_functions_insecure_enclave_app oak_orchestrator

# Build a single enclave app, given its name.
build_enclave_app name:
    env --chdir=enclave_apps/{{name}} cargo build --release

oak_functions_insecure_enclave_app:
    env --chdir=enclave_apps/oak_functions_enclave_app cargo build --release --no-default-features --features=allow_sensitive_logging

oak_restricted_kernel_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --bin=oak_restricted_kernel_bin

_wrap_kernel kernel_bin_prefix:
    #!/usr/bin/env bash
    # This script builds and then wraps a kernel as a bzImage. It outputs the bzimage and its constituent parts for measurement.
    KERNEL_BIN_PREFIX="{{kernel_bin_prefix}}"
    OAK_WRAPPER_DIR="oak_restricted_kernel_wrapper"
    BIN_DIR="${OAK_WRAPPER_DIR}/bin/${KERNEL_BIN_PREFIX}"
    RUST_TARGET_DIR="${OAK_WRAPPER_DIR}/target/x86_64-unknown-none/release"
    KERNEL_BIN_PATH="${RUST_TARGET_DIR}/oak_restricted_kernel_wrapper"

    # Ensure clean state for the binaries. All binaries in "${BIN_DIR}" will be included in any provenances.
    rm -rf "${BIN_DIR}"
    mkdir -p "${BIN_DIR}"

    # Wrap the kernel as a bzImage.
    env --chdir="${OAK_WRAPPER_DIR}" OAK_RESTRICTED_KERNEL_FILE_NAME="${KERNEL_BIN_PREFIX}_bin" cargo build --release

    # Copy the kernel binary to the designated location.
    rust-objcopy --output-target=binary "${KERNEL_BIN_PATH}" "${BIN_DIR}/${KERNEL_BIN_PREFIX}_bzimage"

    # Process the kernel binary using oak_kernel_measurement.
    cargo run --package oak_kernel_measurement -- \
        --kernel="${BIN_DIR}/${KERNEL_BIN_PREFIX}_bzimage" \
        --kernel-setup-data-output="${BIN_DIR}/${KERNEL_BIN_PREFIX}_setup_data" \
        --kernel-image-output="${BIN_DIR}/${KERNEL_BIN_PREFIX}_image"

oak_restricted_kernel_wrapper: oak_restricted_kernel_bin
    just _wrap_kernel oak_restricted_kernel

oak_restricted_kernel_simple_io_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --no-default-features --features=simple_io_channel --bin=oak_restricted_kernel_simple_io_bin

oak_restricted_kernel_simple_io_wrapper: oak_restricted_kernel_simple_io_bin
    just _wrap_kernel oak_restricted_kernel_simple_io

oak_restricted_kernel_simple_io_init_rd_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --no-default-features --features=simple_io_channel,initrd --bin=oak_restricted_kernel_simple_io_init_rd_bin

oak_restricted_kernel_simple_io_init_rd_wrapper: oak_restricted_kernel_simple_io_init_rd_bin
    just _wrap_kernel oak_restricted_kernel_simple_io_init_rd


stage0_bin:
    env --chdir=stage0_bin cargo objcopy --release -- --output-target=binary target/x86_64-unknown-none/release/stage0_bin

stage1_cpio:
    env --chdir=oak_containers_stage1 make

oak_containers_kernel:
    env --chdir=oak_containers_kernel make

oak_containers_system_image:
    env --chdir=oak_containers_system_image DOCKER_BUILDKIT=0 bash build.sh

# Profile the Wasm execution and generate a flamegraph.
profile_wasm:
    # If it fails with SIGSEGV, try running again.
    cargo bench --package=oak_functions_service --bench=wasm_benchmark --features=wasmtime flamegraph -- --profile-time=5
    google-chrome ./target/criterion/flamegraph/profile/flamegraph.svg

# Oak Containers Hello World entry point.

oak_containers_hello_world_container_bundle_tar:
    env --chdir=oak_containers_hello_world_container DOCKER_BUILDKIT=0 bash build_container_bundle

cc_oak_containers_hello_world_container_bundle_tar:
    env bazel build -c opt //cc/containers/hello_world_trusted_app:bundle.tar

oak_containers_hello_world_untrusted_app:
    env cargo build --release --package='oak_containers_hello_world_untrusted_app'

all_oak_containers_binaries: stage0_bin stage1_cpio oak_containers_kernel oak_containers_system_image oak_containers_hello_world_container_bundle_tar cc_oak_containers_hello_world_container_bundle_tar oak_containers_hello_world_untrusted_app

# Oak Functions Containers entry point.

oak_functions_containers_container_bundle_tar:
    env --chdir=oak_functions_containers_container DOCKER_BUILDKIT=0 bash build_container_bundle

oak_functions_containers_launcher:
    env cargo build --release --package='oak_functions_containers_launcher'

all_oak_functions_containers_binaries: stage0_bin stage1_cpio oak_containers_kernel oak_containers_system_image oak_functions_containers_container_bundle_tar oak_functions_containers_launcher

ensure_no_std package:
    RUSTFLAGS="-C target-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float" cargo build --target=x86_64-unknown-none --package='{{package}}'

all_ensure_no_std: (ensure_no_std "micro_rpc") (ensure_no_std "oak_attestation_verification") (ensure_no_std "oak_restricted_kernel_sdk")

# Entry points for Kokoro CI.

kokoro_build_binaries_rust: all_enclave_apps oak_restricted_kernel_bin oak_restricted_kernel_simple_io_bin oak_restricted_kernel_simple_io_wrapper oak_restricted_kernel_simple_io_init_rd_wrapper stage0_bin

kokoro_oak_containers: all_oak_containers_binaries oak_functions_containers_container_bundle_tar
    RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar --package='oak_containers_hello_world_untrusted_app'

kokoro_run_tests: all_ensure_no_std
    RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar --workspace --exclude='oak_containers_hello_world_untrusted_app'

clang-tidy:
    bazel build --config=clang-tidy //cc/...
