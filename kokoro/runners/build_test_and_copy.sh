#!/usr/bin/env bash
echo "[$(date --utc)] Starting $0"

set -o errexit
set -o nounset
set -o pipefail

cd "$(dirname "$0")/../.."
source ./kokoro/runners/helpers.sh

trap collect_test_logs ERR

run_as_test_case "check-format" "just format"
run_as_test_case "clippy" "just bazel-clippy"
run_as_test_case "build-and-test-linux-targets" "just std-crates"
run_as_test_case "build-bare-metal-crates" "just bare-metal-crates"
run_as_test_case "build-wasm-crates" "just wasm-crates"
run_as_test_case "test-codelab" "just test-codelab"
run_as_test_case "benchmarks" "just benchmarks"
run_as_test_case "build-and-test-private-memory" "just private-memory-build-and-copy"
run_as_test_case "copy-oak-artifacts" "just copy-oak-artifacts"
