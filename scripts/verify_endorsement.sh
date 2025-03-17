#!/bin/bash
#
# Copyright 2025 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# Reads a binary package from discoverability storage and runs endorsement
# verification on the package.
#
# Example:
#
# scripts/verify_endorsement.sh \
#    fe25525afee52590d82b953743dd5a25c3439322f018c8a4966a2d3220fe66ef
set -e
set -o pipefail

readonly FILES_PREFIX=https://storage.googleapis.com/oak-files
readonly INDEX_PREFIX=https://storage.googleapis.com/oak-index

# ID of index to retrieve endorsement hashes by binary hashes.
readonly ENDORSEMENT_FOR_BINARY=13

# ID of index to retrieve signature hashes by endorsement hashes.
readonly SIGNATURE_FOR_ENDORSEMENT=14

# ID of index to retrieve log entry hashes by endorsement hashes.
readonly LOGENTRY_FOR_ENDORSEMENT=15

usage_and_exit() {
  >&2 echo "Usage: $0 <binary_hash>"
  exit 1
}

download() {
  local binary_hash="$1"
  local dir="$2"

  endorsement_hash=$(curl --fail --silent \
      "${INDEX_PREFIX}/${ENDORSEMENT_FOR_BINARY}/${binary_hash}" | tail -1)
  signature_hash=$(curl --fail --silent \
      "${INDEX_PREFIX}/${SIGNATURE_FOR_ENDORSEMENT}/${endorsement_hash}")
  # The log entry may not exist, in which case we set it to empty.
  logentry_hash=$(curl --fail --silent \
      "${INDEX_PREFIX}/${LOGENTRY_FOR_ENDORSEMENT}/${endorsement_hash}" || echo "")

  curl --fail --silent --output "${dir}/binary" "${FILES_PREFIX}/${binary_hash}"
  curl --fail --silent --output \
      "${dir}/endorsement.json" \
      "${FILES_PREFIX}/${endorsement_hash}"
  curl --fail --silent --output \
      "${dir}/endorsement.json.sig" \
      "${FILES_PREFIX}/${signature_hash}"
  if [[ -n "${logentry_hash}" ]]; then
    curl --fail --silent --output \
        "${dir}/logentry.json" \
        "${FILES_PREFIX}/${logentry_hash}"
  fi
}

verify() {
  local dir="$1"
  local opts=(
    --endorsement="${dir}/endorsement.json"
    --signature="${dir}/endorsement.json.sig"
    --endorser-public-key=oak_attestation_verification/testdata/endorser_public_key.pem
  )
  if [[ -f "${dir}/logentry.json" ]]; then
    opts+=(
      --log_entry="${dir}/logentry.json"
    )
  fi

  bazel run //oak_attestation_verification:verify_endorsement -- "${opts[@]}"
}

if [[ $# != 1 ]]; then
  usage_and_exit
fi

dir=$(mktemp -d)
>&2 echo "ls -la ${dir}"
download "sha2-256:$1" "${dir}"
ls -la "${dir}" 1>&2
verify "${dir}"
