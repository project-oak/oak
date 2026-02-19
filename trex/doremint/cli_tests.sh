#!/bin/bash

# Tests that exercise the CLI, especially flag parsing code.

# Do not exit on error, so we can run all tests and report failures.
set +e

CLAIMS_FILE="./trex/doremint/testdata/claims.toml"
GOLDEN_FILE="./trex/doremint/testdata/golden.json"
BLOB_FILE="./trex/doremint/testdata/dummy_blob.txt"

# If there's any failure, this will be set to 1.
overall_status=0

# A generic test runner that prints a single status line.
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
  local output_index="${repository_dir}/index.json"

  ${CLI} blob endorse \
    --file="${BLOB_FILE}" \
    --claims-toml="${CLAIMS_FILE}" \
    --valid-for=24h \
    --issued-on=2025-01-01T00:00:00Z \
    --repository="${repository_dir}"

  # Check for existence and non-emptiness of the generated index.json.
  test -s "${output_index}"

  # Check for existence of subject, statement, and bundle blobs.
  # These paths are derived from dummy_blob.txt content and hardcoded statement/bundle.
  # Ideally, we would parse output_index and verify digests dynamically.
  test -f "${repository_dir}/blobs/sha256/8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06"
  test -f "${repository_dir}/blobs/sha256/b9e0cbf6941ea66dd6cedecfa5a571f1e638d44960a32fe0552bca2862d1394e"
  # The actual digest of the cosign bundle is dynamic, so we can't hardcode it.
  # We'll rely on the `doremint` command itself to report success and verify the files were stashed.
}

# shellcheck disable=SC2329
test_blob_endorse_digest() {
  set -e
  local repository_dir=$(mktemp -d)
  local output_index="${repository_dir}/index.json"
  local blob_digest="sha256:8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06"

  ${CLI} blob endorse \
    --digest="${blob_digest}" \
    --claims-toml="${CLAIMS_FILE}" \
    --valid-for=24h \
    --issued-on=2025-01-01T00:00:00Z \
    --repository="${repository_dir}"

  # Check for existence of index.json
  test -s "${output_index}"

  # Subject blob should NOT exist
  if [ -f "${repository_dir}/blobs/sha256/8185390ae641622463edb22af96b5e957759f639b27998d47e28b223916adb06" ]; then
    echo "Subject blob should not exist when endorsing by digest" >&2
    return 1
  fi
}

# shellcheck disable=SC2329
test_blob_endorse_index_content() {
  set -e
  local repository_dir=$(mktemp -d)
  local output_index="${repository_dir}/index.json"

  ${CLI} blob endorse \
    --file="${BLOB_FILE}" \
    --claims-toml="${CLAIMS_FILE}" \
    --valid-for=24h \
    --issued-on=2025-01-01T00:00:00Z \
    --repository="${repository_dir}"

  # Verify cas_clients field in index.json.
  # z00767225522304297082 is the renamed field for cas_clients.
  # z12941845592822707391 is the tag field for CASClient.
  # z05040460528458638259 is the renamed OCI variant.
  # z03515109587559058051 is the renamed url field.
  grep -q '"z00767225522304297082":' "${output_index}"
  grep -q '"z12941845592822707391": "z05040460528458638259"' "${output_index}"
  grep -q '"z03515109587559058051": "./blobs"' "${output_index}"
}

run test_default_issued_at_flag
run test_output_flag
run test_stdout
run test_blob_help
run test_blob_endorse
run test_blob_endorse_digest
run test_blob_endorse_index_content

exit ${overall_status}
