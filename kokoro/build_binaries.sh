#!/usr/bin/env bash

# NOTE: This is WIP. For now it only builds a single binary. Once we are
# certain this approach works, we will update it to build all binaries.

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

export CI=kokoro

export RUST_BACKTRACE=1
export RUST_LOG=debug
export XDG_RUNTIME_DIR=/var/run

./scripts/docker_pull
./scripts/docker_run  nix develop .#rust --command env --chdir=oak_restricted_kernel_bin cargo build --release

# Copy the generated binary to placer
cp ./oak_restricted_kernel_bin/target/x86_64-unknown-none/release/oak_restricted_kernel_bin "$KOKORO_ARTIFACTS_DIR/latest/oak_restricted_kernel_bin/${KOKORO_GIT_COMMIT_oak:?}"
ls -als "$KOKORO_ARTIFACTS_DIR"
