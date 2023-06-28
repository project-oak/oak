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
# --all-targets is needed to also run tests for examples and benches.
./scripts/docker_run nix develop .#ci --command cargo nextest run --all-targets --hide-progress-bar

mkdir "$KOKORO_ARTIFACTS_DIR/test_logs/"
cp ./target/nextest/default/*.xml "$KOKORO_ARTIFACTS_DIR/test_logs/"
ls -als "$KOKORO_ARTIFACTS_DIR"
