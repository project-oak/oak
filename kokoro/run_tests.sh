#!/usr/bin/env bash

# shellcheck source=./kokoro/helpers/common.sh
source "$(dirname "$0")/helpers/common.sh"

upload_test_logs() {
    mkdir -p "${KOKORO_ARTIFACTS_DIR}/test_logs/"
    cp --preserve=timestamps \
        ./target/nextest/default/*.xml \
        "${KOKORO_ARTIFACTS_DIR}/test_logs/" || true

    kokoro_cleanup
}

trap upload_test_logs EXIT

./scripts/docker_pull
./scripts/docker_run nix develop .#default --command just kokoro_run_cargo_tests
./scripts/git_check_diff
