#!/usr/bin/env bash

# shellcheck source=./kokoro/helpers/common.sh
source "$(dirname "$0")/helpers/common.sh"

./scripts/docker_pull
./scripts/docker_run nix develop .#ci --command just kokoro_verify_buildconfigs
./scripts/git_check_diff
