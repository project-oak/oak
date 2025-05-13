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

# Contains constants and functions for endorsement verification. Do not invoke.
#
# Suppress warnings about unused variables in entire file. We don't want to
# export these constants.
# shellcheck disable=SC2034
readonly DEFAULT_FBUCKET=oak-files
readonly DEFAULT_IBUCKET=oak-index

readonly URL_PREFIX=https://storage.googleapis.com

# ID of index to retrieve signature hashes by endorsement hashes.
readonly SIGNATURE_FOR_ENDORSEMENT=14

# ID of index to retrieve log entry hashes by endorsement hashes.
readonly LOGENTRY_FOR_ENDORSEMENT=15

# ID of index to retrieve the public key hash from the signature hash.
readonly PK_FOR_SIGNATURE=16

# ID of index to retrieve endorsement hashes by public key hashes.
readonly ENDORSEMENTS_FOR_PK=21

readonly PUBLISHED_CLAIM_TYPE="https://github.com/project-oak/oak/blob/main/docs/tr/claim/52637.md"
readonly RUNNABLE_CLAIM_TYPE="https://github.com/project-oak/oak/blob/main/docs/tr/claim/68317.md"
readonly OPEN_SOURCE_CLAIM_TYPE="https://github.com/project-oak/oak/blob/main/docs/tr/claim/92939.md"

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
