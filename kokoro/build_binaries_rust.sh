#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

export CI=kokoro
export RUST_BACKTRACE=1
export RUST_LOG=debug
export XDG_RUNTIME_DIR=/var/run

# Make sure we're in the root of the repository.
cd "$(dirname "$0")/.."

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
    ./oak_restricted_kernel_bin/target/x86_64-unknown-none/release/oak_restricted_kernel_bin
    ./oak_restricted_kernel_bin/target/x86_64-unknown-none/release/oak_restricted_kernel_simple_io_bin
    ./oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_simple_io_wrapper_bin
    ./stage0_bin/target/x86_64-unknown-none/release/stage0_bin
    ./enclave_apps/target/x86_64-unknown-none/release/key_xor_test_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_echo_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_echo_raw_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_functions_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_functions_insecure_enclave_app
)
cp --preserve=timestamps \
    "${generated_binaries[@]}" \
    "${KOKORO_ARTIFACTS_DIR}/binaries/"

ls -alsR "${KOKORO_ARTIFACTS_DIR}/binaries"
