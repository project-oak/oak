#!/usr/bin/env bash
echo "[$(date --utc)] Starting $0"

set -o errexit
set -o nounset
set -o pipefail

cd "$(dirname "$0")/../.."
source ./kokoro/helpers/common.sh

trap collect_test_logs ERR

just format-all
just bazel-clippy
just std-crates
just bare-metal-crates
just wasm-crates
just test-codelab
just private-memory-build-and-copy
just copy-oak-artifacts
