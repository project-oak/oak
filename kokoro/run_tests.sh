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
./scripts/docker_run nix develop .#default --command just kokoro_run_tests

mkdir -p "$KOKORO_ARTIFACTS_DIR/test_logs/"
cp ./target/nextest/default/*.xml "$KOKORO_ARTIFACTS_DIR/test_logs/" || true
