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
./scripts/docker_run nix develop .#default --command just clippy-ci
./scripts/git_check_diff
