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

# Lists and retrieves package metdata from discoverability storage and runs
# endorsement verification on selected packages. This operates in terms of
# endorsements only - actual binaries are not involved, but can still be
# downloaded from the files bucket.
#
# Requires: curl, python3, sha256sum
set -e
set -o pipefail

readonly FILES_PREFIX=https://storage.googleapis.com/oak-files
readonly INDEX_PREFIX=https://storage.googleapis.com/oak-index

# ID of index to retrieve signature hashes by endorsement hashes.
readonly SIGNATURE_FOR_ENDORSEMENT=14

# ID of index to retrieve log entry hashes by endorsement hashes.
readonly LOGENTRY_FOR_ENDORSEMENT=15

# ID of index to retrieve the public key hash from the signature hash.
readonly PK_FOR_SIGNATURE=16

# ID of index to retrieve endorsement hashes by public key hashes.
readonly ENDORSEMENTS_FOR_PK=21

readonly NANOS_PER_DAY=$((24 * 3600 * 1000 * 1000 * 1000))

usage_and_exit() {
  >&2 echo "Usage:"
  >&2 echo "  $0 --key_file $HOME/public_key.pem"
  >&2 echo "  $0 --endorsement_hash sha2-256:0cb3e0457eae486ecbc42e553f1ec8327691ae836692e080a1aa191d29b2a121"
  >&2 echo "These modes are mutually exclusive. The first mode lists endorsement"
  >&2 echo "hashes that can go as input to the second mode."

  exit 1
}

# Fetches a file from the files bucket and double checks the hash.
fetch_file() {
  local hash="$1"
  local path="$2"
  curl --fail --silent --output "${path}" "${FILES_PREFIX}/${hash}"
  local actual_hash="sha2-256:$(sha256sum "${path}" | cut -d " " -f 1)"
  if [[ "${hash}" != "${actual_hash}" ]]; then
    >&2 echo "Digest mismatch for ${path}: expected ${hash}, got ${actual_hash}"
    exit 1
  fi
}

readonly JSON_PARSER="import sys, json
e = json.load(sys.stdin)
print(
  e['subject'][0]['name'],
  e['subject'][0]['digest']['sha256'],
  e['predicate']['validity']['notAfter'])"

timestamp() {
  date "+%s%N" --date="$1"
}

now_timestamp() {
  date "+%s%N"
}

list_all_endorsements() {
  local keyfile="$1"
  local pk_hash="sha2-256:$(sha256sum "${keyfile}" | cut -d " " -f 1)"
  local endorsement_hashes=$(curl --fail --silent \
    "${INDEX_PREFIX}/${ENDORSEMENTS_FOR_PK}/${pk_hash}")
  local now=$(now_timestamp)
  local tmp_path=$(mktemp)
  for endorsement_hash in ${endorsement_hashes}; do
    # Only proceed when the key used to lookup coincides with the key used
    # to make the signature.
    local signature_hash=$(curl --fail --silent \
        "${INDEX_PREFIX}/${SIGNATURE_FOR_ENDORSEMENT}/${endorsement_hash}")
    local actual_pk_hash=$(curl --fail --silent \
        "${INDEX_PREFIX}/${PK_FOR_SIGNATURE}/${signature_hash}")
    if [[ "${pk_hash}" != "${actual_pk_hash}" ]]; then
      >&2 echo "Key digest mismatch: expected ${pk_hash}, got ${actual_pk_hash}"
      exit 1
    fi

    echo "${endorsement_hash}"
    fetch_file "${endorsement_hash}" "${tmp_path}"
    local endorsement=$(cat "${tmp_path}")
    read -r subject_name subject_hash not_after <<< \
        "$(echo "${endorsement}" | python3 -c "${JSON_PARSER}")"
    local days=$(( ($(timestamp "${not_after}") - now) / "${NANOS_PER_DAY}" ))
    echo "    Subject name:   ${subject_name}"
    echo "    Subject hash:   sha2-256:${subject_hash}"
    echo "    Days remaining: ${days}"
  done
}

download() {
  local endorsement_hash="$1"
  local dir="$2"

  local signature_hash=$(curl --fail --silent \
      "${INDEX_PREFIX}/${SIGNATURE_FOR_ENDORSEMENT}/${endorsement_hash}")
  local pk_hash=$(curl --fail --silent \
      "${INDEX_PREFIX}/${PK_FOR_SIGNATURE}/${signature_hash}")
  # The log entry may not exist, in which case we set it to empty.
  local logentry_hash=$(curl --fail --silent \
      "${INDEX_PREFIX}/${LOGENTRY_FOR_ENDORSEMENT}/${endorsement_hash}" || echo "")

  fetch_file "${endorsement_hash}" "${dir}/endorsement.json"
  fetch_file "${signature_hash}" "${dir}/endorsement.json.sig"
  fetch_file "${pk_hash}" "${dir}/endorser_public_key.pem"
  if [[ -n "${logentry_hash}" ]]; then
    fetch_file "${logentry_hash}" "${dir}/logentry.json"
  fi
}

verify() {
  local dir="$1"
  local opts=(
    --endorsement="${dir}/endorsement.json"
    --signature="${dir}/endorsement.json.sig"
    --endorser-public-key="${dir}/endorser_public_key.pem"
  )
  if [[ -f "${dir}/logentry.json" ]]; then
    opts+=(
      --log_entry="${dir}/logentry.json"
    )
  fi

  bazel run //oak_attestation_verification:verify_endorsement -- "${opts[@]}"
}

download_verify() {
  local endorsement_hash="$1"

  local dir=$(mktemp -d)
  >&2 echo "ls -la ${dir}"
  download "${endorsement_hash}" "${dir}"
  ls -la "${dir}" 1>&2
  verify "${dir}"
}

trap usage_and_exit ERR # When shift fails
while [[ $# -gt 0 ]]; do
  case "$1" in
    --key_file)
      shift
      keyfile="$1"
      shift
      list_all_endorsements "${keyfile}"
      ;;
    --endorsement_hash)
      shift
      endorsement_hash="$1"
      shift
      download_verify "${endorsement_hash}"
      ;;
    *)
      usage_and_exit
      ;;
  esac
done
