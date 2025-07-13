#!/bin/bash

# Tests that exercise the CLI, esepcially flag parsing code.

# Do not exit on error, so we can run all tests and report failures.
set +e

# The path to the CLI, as seen from the test's runfiles directory.
CLAIMS_FILE="./doremint/testdata/claims.toml"
GOLDEN_FILE="./doremint/testdata/golden.json"

# If there's any failure, this will be set to 1.
overall_status=0

# A generic test runner that prints a single status line.
run() {
    local test_name=$1
    # Use a subshell to execute the test and capture its output and exit code.
    if test_output=$($test_name 2>&1); then
        echo "TEST: $test_name ... PASS" >&2
    else
        echo "TEST: $test_name ... FAIL" >&2
        echo "--- FAILURE OUTPUT for $test_name ---" >&2
        echo "$test_output" >&2
        echo "------------------------------------" >&2
        overall_status=1
    fi
}

# shellcheck disable=SC2317
test_default_issued_at_flag() {
    # `set -e` inside the function ensures that it fails on the first error.
    set -e
    local output_file=$(mktemp)

    # Time is hard to test, so we just test that it doesn't fail
    $CLI --output="$output_file" image endorse \
      --image-ref=example.com/app \
      --image-digest=sha256:deadbeef \
      --valid-for=24h \
      --claims-file="$CLAIMS_FILE"
}

# shellcheck disable=SC2317
test_output_flag() {
    # `set -e` inside the function ensures that it fails on the first error.
    set -e
    local output_file=$(mktemp)    

    $CLI --output="$output_file" image endorse \
      --image-ref=example.com/app \
      --image-digest=sha256:deadbeef \
      --valid-for=24h \
      --claims-file="$CLAIMS_FILE" \
      --issued-on=2025-01-01T00:00:00Z

    diff "$GOLDEN_FILE" "$output_file"
}

# shellcheck disable=SC2317
test_stdout() {
    set -e
    local output_file=$(mktemp)

    $CLI image endorse \
      --image-ref=example.com/app \
      --image-digest=sha256:deadbeef \
      --valid-for=24h \
      --claims-file="$CLAIMS_FILE" \
      --issued-on=2025-01-01T00:00:00Z > "$output_file"

    diff "$GOLDEN_FILE" "$output_file"
}

run test_default_issued_at_flag
run test_output_flag
run test_stdout

exit $overall_status