#!/usr/bin/env bash

# shellcheck source=./kokoro/common.sh
source "$(dirname "$0")/common.sh"

./scripts/docker_pull
./scripts/docker_run nix develop .#ci --command just kokoro_build_binaries_rust

mkdir -p "${KOKORO_ARTIFACTS_DIR}/test_logs/"
cp --preserve=timestamps \
    ./target/nextest/default/*.xml \
    "${KOKORO_ARTIFACTS_DIR}/test_logs/" || true

mkdir -p "${KOKORO_ARTIFACTS_DIR}/binaries/"

# Store the git commit hash in the name of an empty file, so that it can be
# efficiently found via a glob.
touch "${KOKORO_ARTIFACTS_DIR}/binaries/git_commit_${KOKORO_GIT_COMMIT_oak:?}"

# Copy the generated binaries to Placer. The timestamps are used to convey
# the creation time.
readonly generated_binaries=(
    ./oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_simple_io_init_rd_wrapper_bin
    ./oak_restricted_kernel_wrapper/cmd_line_regex.txt
    ./stage0_bin/target/x86_64-unknown-none/release/stage0_bin
    ./enclave_apps/target/x86_64-unknown-none/release/key_xor_test_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_echo_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_echo_raw_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_functions_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_functions_insecure_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_orchestrator
)
readonly binary_names=(
    oak_restricted_kernel_simple_io_init_rd_wrapper_bin
    oak_restricted_kernel_simple_io_wrapper_cmd_line_regex
    stage0_bin
    key_xor_test_app
    oak_echo_enclave_app
    oak_echo_raw_enclave_app
    oak_functions_enclave_app
    oak_functions_insecure_enclave_app
    oak_orchestrator
)
for i in "${!binary_names[@]}"; do
    cp --preserve=timestamps \
        "${generated_binaries[$i]}" \
        "${KOKORO_ARTIFACTS_DIR}/binaries/${binary_names[$i]}"
done

ls -alsR "${KOKORO_ARTIFACTS_DIR}/binaries"

# Print binary digests (ignore failures, e.g. for directories).
sha256sum "${KOKORO_ARTIFACTS_DIR}"/binaries/* || true
