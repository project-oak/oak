#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

export CI=kokoro

export RUST_BACKTRACE=1
export RUST_LOG=debug
export XDG_RUNTIME_DIR=/var/run

./scripts/docker_pull
./scripts/docker_run nix develop .#ci --command just kokoro

mkdir -p "$KOKORO_ARTIFACTS_DIR/test_logs/"
cp ./target/nextest/default/*.xml "$KOKORO_ARTIFACTS_DIR/test_logs/"

mkdir -p "$KOKORO_ARTIFACTS_DIR/binaries/"

# Store the git commit hash in a file.
echo "${KOKORO_GIT_COMMIT_oak:?}" > "$KOKORO_ARTIFACTS_DIR/binaries/git_commit"

# Copy the generated binaries to Placer.
export GENERATED_BINARIES=(
    ./oak_restricted_kernel_bin/target/x86_64-unknown-none/release/oak_restricted_kernel_bin
    ./stage0_bin/target/x86_64-unknown-none/release/stage0_bin
    ./enclave_apps/target/x86_64-unknown-none/release/oak_echo_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_echo_raw_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_functions_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/oak_tensorflow_enclave_app
    ./enclave_apps/target/x86_64-unknown-none/release/quirk_echo_enclave_app
)
cp "${GENERATED_BINARIES[@]}" "$KOKORO_ARTIFACTS_DIR/binaries/"

ls -alsR "$KOKORO_ARTIFACTS_DIR/binaries"
