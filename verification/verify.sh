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

# Retrieves package metdata from discoverability storage and runs
# endorsement verification on the selected package. This operates in terms of
# endorsements only - actual binaries are not involved, but can still be
# downloaded from the files bucket.
#
# Requires: curl, sha256sum
set -e
set -o pipefail

# shellcheck source=verification/common.sh
source "$(dirname "$0")/common.sh"

usage_and_exit() {
  >&2 echo "Usage:"
  >&2 echo "  $0 --endorsement_hash sha2-256:0cb3e0457eae486ecbc42e553f1ec8327691ae836692e080a1aa191d29b2a121"
  >&2 echo "Verifies a binary package by endorsement hash."
  exit 1
}

# Fetches a file from the files bucket and double checks the hash.
fetch_file() {
  local fbucket="$1"
  local hash="$2"
  local path="$3"
  curl --fail --silent --output "${path}" "${URL_PREFIX}/${fbucket}/${hash}"
  local actual_hash="sha2-256:$(sha256sum "${path}" | cut -d " " -f 1)"
  if [[ "${hash}" != "${actual_hash}" ]]; then
    >&2 echo "Digest mismatch for ${path}: expected ${hash}, got ${actual_hash}"
    exit 1
  fi
}

download() {
  local fbucket="$1"
  local ibucket="$2"
  local endorsement_hash="$3"
  local dir="$4"
  local ibucket_prefix="${URL_PREFIX}/${ibucket}"

  local signature_hash pk_hash
  signature_hash=$(curl --fail --silent \
      "${ibucket_prefix}/${SIGNATURE_FOR_ENDORSEMENT}/${endorsement_hash}")
  pk_hash=$(curl --fail --silent \
      "${ibucket_prefix}/${PK_FOR_SIGNATURE}/${signature_hash}")
  # The log entry may not exist, in which case we set it to empty.
  local logentry_hash=$(curl --fail --silent \
      "${ibucket_prefix}/${LOGENTRY_FOR_ENDORSEMENT}/${endorsement_hash}" || echo "")

  fetch_file "${fbucket}" "${endorsement_hash}" "${dir}/endorsement.json"
  fetch_file "${fbucket}" "${signature_hash}" "${dir}/endorsement.json.sig"
  fetch_file "${fbucket}" "${pk_hash}" "${dir}/endorser_public_key.pem"
  if [[ -n "${logentry_hash}" ]]; then
    fetch_file "${fbucket}" "${logentry_hash}" "${dir}/logentry.json"
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
  local fbucket="$1"
  local ibucket="$2"
  local endorsement_hash="$3"

  local dir=$(mktemp -d)
  >&2 echo "ls -la ${dir}"
  download "${fbucket}" "${ibucket}" "${endorsement_hash}" "${dir}"
  ls -la "${dir}" 1>&2
  verify "${dir}"
}

trap usage_and_exit ERR # When shift fails
fbucket="${DEFAULT_FBUCKET}"
ibucket="${DEFAULT_IBUCKET}"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --fbucket)
      shift
      fbucket="$1"
      shift
      ;;
    --ibucket)
      shift
      ibucket="$1"
      shift
      ;;
    --endorsement_hash)
      shift
      endorsement_hash="$1"
      shift
      download_verify "${fbucket}" "${ibucket}" "${endorsement_hash}"
      ;;
    *)
      usage_and_exit
      ;;
  esac
done
