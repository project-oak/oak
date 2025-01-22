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

./scripts/docker_pull
./scripts/docker_run nix develop .#ci --command just kokoro_verify_buildconfigs
./scripts/git_check_diff

kokoro_cleanup
