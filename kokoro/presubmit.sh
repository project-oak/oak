#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

export CI=kokoro

export RUST_BACKTRACE=1
export RUST_LOG=debug

./scripts/docker_pull
./scripts/docker_run cargo nextest run --hide-progress-bar \
  --package=oak_functions_launcher \
  --package=quirk_echo_launcher

cp ./target/nextest/default/junit.xml "$KOKORO_ARTIFACTS_DIR/"
ls -als "$KOKORO_ARTIFACTS_DIR"
