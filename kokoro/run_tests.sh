#!/usr/bin/env bash
echo "[$(date --utc)] Starting $0"

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

# Make sure we're in the root of the repository.
cd "$(dirname "$0")/.."

# shellcheck source=kokoro/helpers/common.sh
source kokoro/helpers/common.sh

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
