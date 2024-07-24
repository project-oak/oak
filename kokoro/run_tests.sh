#!/usr/bin/env bash

# shellcheck source=./kokoro/common.sh
source "$(dirname "$0")/common.sh"

./scripts/docker_pull
./scripts/docker_run nix develop .#default --command just kokoro_run_cargo_tests
./scripts/git_check_diff

mkdir -p "${KOKORO_ARTIFACTS_DIR}/test_logs/"
cp --preserve=timestamps \
    ./target/nextest/default/*.xml \
    "${KOKORO_ARTIFACTS_DIR}/test_logs/" || true
