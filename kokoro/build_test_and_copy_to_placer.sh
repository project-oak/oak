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

configure_common_env
configure_bazelrc

./scripts/docker_pull
# TODO: b/337266665 - Remove bazel-cache-test logic once we are satisfied with remote cache hits.
./scripts/docker_run nix develop .#default --command ./kokoro/runners/build_test_and_copy.sh
./scripts/git_check_diff

# System image deps (oak_containers_orchestrator, oak_containers_syslogd,
# oak_containers_agent) are tracked to monitor their reproducibility. They are
# expected to be imported transiently into google3 for the sake of provenance
# verification (i.e., do Kokoro and GitHub produce identical results).
# Print binary digests (ignore failures, e.g. for directories).
find "artifacts/binaries" -exec sha256sum {} \;

# Store the git commit hash in the name of an empty file, so that it can
# be efficiently found via a glob.
touch "artifacts/binaries/git_commit_${KOKORO_GIT_COMMIT_oak:?}"
