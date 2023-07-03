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
./scripts/docker_run nix develop .#containers --command just kokoro_oak_containers

mkdir -p "$KOKORO_ARTIFACTS_DIR/test_logs/"
cp ./target/nextest/default/*.xml "$KOKORO_ARTIFACTS_DIR/test_logs/" || true

mkdir -p "$KOKORO_ARTIFACTS_DIR/binaries/"

# Store the git commit hash in a file.
echo "${KOKORO_GIT_COMMIT_oak:?}" > "$KOKORO_ARTIFACTS_DIR/binaries/git_commit"

# Copy the generated binaries to Placer.
export GENERATED_BINARIES=(
    ./target/stage1.cpio
    ./oak_containers_kernel/target/vmlinux-6.1.33
    ./oak_containers_system_image/target/image.tar
)
cp "${GENERATED_BINARIES[@]}" "$KOKORO_ARTIFACTS_DIR/binaries/"

ls -alsR "$KOKORO_ARTIFACTS_DIR/binaries"
