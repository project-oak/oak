#!/bin/bash

# Tests that exercise the CLI, especially flag parsing code.

# Do not exit on error, so we can run all tests and report failures.
set +e

CLAIMS_FILE="./trex/doremint/testdata/claims.toml"
GOLDEN_FILE="./trex/doremint/testdata/golden.json"
BLOB_FILE="./trex/doremint/testdata/dummy_blob.txt"

# Directory index names. Defined in trex/client/src/lib.rs.
SUBJECT_TO_STATEMENT_INDEX="z02559989796713244320"
STATEMENT_TO_BUNDLE_INDEX="z05735596614295417312"

# If there's any failure, this will be set to 1.
overall_status=0

# Assertion helpers that print a message on failure.
# shellcheck disable=SC2329
assert_file_not_empty() {
  if ! test -s "${1}"; then
    echo "ASSERT: expected non-empty file: ${1}" >&2
    return 1
  fi
}

# shellcheck disable=SC2329
assert_file_exists() {
  if ! test -f "${1}"; then
    echo "ASSERT: expected file to exist: ${1}" >&2
    return 1
  fi
}

# shellcheck disable=SC2329
assert_file_not_exists() {
  if test -f "${1}"; then
    echo "ASSERT: expected file to NOT exist: ${1}" >&2
    return 1
  fi
}

# shellcheck disable=SC2329
assert_grep() {
  if ! grep -q "${1}" "${2}"; then
    echo "ASSERT: expected pattern '${1}' in file: ${2}" >&2
    echo "  File contents:" >&2
    cat "${2}" >&2
    return 1
  fi
}

# A generic test runner that prints a single status line.
# shellcheck disable=SC2329
run() {
  local test_name=${1}
  # Use a subshell to execute the test and capture its output and exit code.
  if test_output=$(${test_name} 2>&1); then
    echo "TEST: ${test_name} ... PASS" >&2
  else
    echo "TEST: ${test_name} ... FAIL" >&2
    echo "--- FAILURE OUTPUT for ${test_name} ---" >&2
    echo "${test_output}" >&2
    echo "------------------------------------" >&2
    overall_status=1
  fi
}

# shellcheck disable=SC2329
test_default_issued_at_flag() {
  # `set -e` inside the function ensures that it fails on the first error.
  set -e
  local output_file=$(mktemp)

  # Time is hard to test, so we just test that it doesn't fail
  ${CLI} image endorse \
    --image=example.com/app@sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff \
    --valid-for=24h \
    --claims-toml="${CLAIMS_FILE}" \
    --output="${output_file}"
}

# shellcheck disable=SC2329
test_output_flag() {
  # `set -e` inside the function ensures that it fails on the first error.
  set -e
  local output_file=$(mktemp)

  ${CLI} image endorse \
    --image=example.com/app@sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff \
    --valid-for=24h \
    --claims-toml="${CLAIMS_FILE}" \
    --issued-on=2025-01-01T00:00:00Z \
    --output="${output_file}"

  diff "${GOLDEN_FILE}" "${output_file}"
}

# shellcheck disable=SC2329
test_stdout() {
  set -e
  local output_file=$(mktemp)

  ${CLI} image endorse \
    --image=example.com/app@sha256:ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff \
    --valid-for=24h \
    --claims-toml="${CLAIMS_FILE}" \
    --issued-on=2025-01-01T00:00:00Z >"${output_file}"

  diff "${GOLDEN_FILE}" "${output_file}"
}

# shellcheck disable=SC2329
test_blob_help() {
  set -e
  ${CLI} blob --help >/dev/null
  ${CLI} blob endorse --help >/dev/null
}

# shellcheck disable=SC2329
test_blob_endorse() {
  set -e
  local repository_dir=$(mktemp -d)

  ${CLI} blob endorse \
    --file="${BLOB_FILE}" \
    --claims-toml="${CLAIMS_FILE}" \
    --valid-for=24h \
    --issued-on=2025-01-01T00:00:00Z \
    --repository="${repository_dir}"

  # Check for existence of subject, statement, and bundle blobs.
  # These paths are derived from dummy_blob.txt content and hardcoded statement/bundle.
  # ideally, we would parse output_index and verify digests dynamically.
  # Subject: sha256:8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06
  assert_file_not_empty "${repository_dir}/blobs/sha2-256:8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06"
  # Statement: sha256:b9e0cbf6941ea66dd6cedecfa5a571f1e638d44960a32fe0552bca2862d1394e
  assert_file_not_empty "${repository_dir}/blobs/sha2-256:b9e0cbf6941ea66dd6cedecfa5a571f1e638d44960a32fe0552bca2862d1394e"

  # Check for index entry for the subject.
  # Subject Digest Hex: 8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06
  # Statement Digest Hex: b9e0cbf6941ea66dd6cedecfa5a571f1e638d44960a32fe0552bca2862d1394e
  local index_file="${repository_dir}/${SUBJECT_TO_STATEMENT_INDEX}/sha2-256:8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06"
  assert_file_exists "${index_file}"
  assert_grep "b9e0cbf6941ea66dd6cedecfa5a571f1e638d44960a32fe0552bca2862d1394e" "${index_file}"
}

# shellcheck disable=SC2329
test_blob_endorse_digest() {
  set -e
  local repository_dir=$(mktemp --directory)
  local blob_digest="sha256:8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06"

  ${CLI} blob endorse \
    --digest="${blob_digest}" \
    --claims-toml="${CLAIMS_FILE}" \
    --valid-for=24h \
    --issued-on=2025-01-01T00:00:00Z \
    --repository="${repository_dir}"

  # Subject blob should NOT exist when endorsing by digest.
  assert_file_not_exists "${repository_dir}/blobs/sha2-256:8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06"

  # The subject→statement index entry should exist.
  local index_file="${repository_dir}/${SUBJECT_TO_STATEMENT_INDEX}/sha2-256:8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06"
  assert_file_exists "${index_file}"

  # Read the statement digest from the index and verify the statement blob exists.
  local statement_digest
  statement_digest=$(head -1 "${index_file}")
  assert_file_not_empty "${repository_dir}/blobs/${statement_digest}"

  # The statement→bundle index entry should exist.
  local bundle_index_file="${repository_dir}/${STATEMENT_TO_BUNDLE_INDEX}/${statement_digest}"
  assert_file_exists "${bundle_index_file}"

  # Read the bundle digest from the index and verify the bundle blob exists.
  local bundle_digest
  bundle_digest=$(head -1 "${bundle_index_file}")
  assert_file_not_empty "${repository_dir}/blobs/${bundle_digest}"
}

run test_default_issued_at_flag
run test_output_flag
run test_stdout
run test_blob_help
run test_blob_endorse
run test_blob_endorse_digest

exit ${overall_status}
