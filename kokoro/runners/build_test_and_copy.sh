#!/usr/bin/env bash
echo "[$(date --utc)] Starting $0"

set -o errexit
set -o nounset
set -o pipefail

cd "$(dirname "$0")/../.."
source ./kokoro/helpers/common.sh

trap 'print_timing_summary; collect_test_logs' ERR

record_start_time "docker+nix setup" "${1:-}"
time_step "format-all" just format-all
time_step "bazel-clippy" just bazel-clippy
time_step "std-crates" just std-crates
time_step "bare-metal-crates" just bare-metal-crates
time_step "wasm-crates" just wasm-crates
time_step "test-codelab" just test-codelab
time_step "private-memory-build-and-copy" just private-memory-build-and-copy
time_step "copy-oak-artifacts" just copy-oak-artifacts

print_timing_summary
