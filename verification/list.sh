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

# Lists endorsements on discoverability storage.
#
# Requires: curl, python3, sha256sum
set -e
set -o pipefail

# shellcheck source=verification/common.sh
source "$(dirname "$0")/common.sh"

readonly MPM_CLAIM_TYPE=https://github.com/project-oak/oak/blob/main/docs/tr/claim/31543.md
readonly NANOS_PER_DAY=$((24 * 3600 * 1000 * 1000 * 1000))
readonly GREEN="\033[1;32m" # Boldface
readonly PURPLE="\033[1;35m" # Boldface
readonly COLOFF="\033[0m"

usage_and_exit() {
  >&2 echo "Usage:"
  >&2 echo "  $0 --key_file $HOME/public_key.pem"
  >&2 echo "Lists endorsement hashes that can go as input to verify.sh."
  exit 1
}

readonly JSON_PARSER="import sys, json
e = json.load(sys.stdin)
s = e['subject'][0]
p = e['predicate']
claim_types = []
if 'claims' in p:
  claim_types = [claim['type'] for claim in p['claims']]
print(
    s['name'], s['digest']['sha256'],
    p['validity']['notAfter'], ' '.join(claim_types))"

timestamp() {
  date "+%s%N" --date="$1"
}

now_timestamp() {
  date "+%s%N"
}

list_all_endorsements() {
  local fbucket="$1"
  local ibucket="$2"
  local keyfile="$3"
  local ibucket_prefix="${URL_PREFIX}/${ibucket}"
  local pk_hash="sha2-256:$(sha256sum "${keyfile}" | cut -d " " -f 1)"

  # We need to make sure failures of curl are fatal.
  # See https://unix.stackexchange.com/questions/23026
  local endorsement_hashes signature_hash actual_pk_hash pkg_name version_id
  endorsement_hashes=$(curl --fail --silent \
      "${ibucket_prefix}/${ENDORSEMENTS_FOR_PK}/${pk_hash}")
  local now=$(now_timestamp)
  local endorsement_path=$(mktemp)
  for endorsement_hash in ${endorsement_hashes}; do
    # Only proceed when the key used to lookup coincides with the key used
    # to make the signature.
    signature_hash=$(curl --fail --silent \
        "${ibucket_prefix}/${SIGNATURE_FOR_ENDORSEMENT}/${endorsement_hash}")
    actual_pk_hash=$(curl --fail --silent \
        "${ibucket_prefix}/${PK_FOR_SIGNATURE}/${signature_hash}")
    if [[ "${pk_hash}" != "${actual_pk_hash}" ]]; then
      >&2 echo "Key digest mismatch: expected ${pk_hash}, got ${actual_pk_hash}"
      exit 1
    fi

    echo -e "${GREEN}${endorsement_hash}${COLOFF}"
    fetch_file "${fbucket}" "${endorsement_hash}" "${endorsement_path}"
    local endorsement=$(cat "${endorsement_path}")
    read -r subject_name subject_hash not_after claim_types_full <<< \
        "$(echo "${endorsement}" | python3 -c "${JSON_PARSER}")"
    read -r -a claim_types <<< "${claim_types_full}"
    subject_hash="sha2-256:${subject_hash}"
    local days=$(( ($(timestamp "${not_after}") - now) / "${NANOS_PER_DAY}" ))
    echo "    Subject name:   ${subject_name}"
    echo "    Subject hash:   ${subject_hash}"
    echo "    Days remaining: ${days}"
    local claims_label="    Claims:         "
    for claim in "${claim_types[@]}"; do
      echo "${claims_label}${claim}"
      claims_label="                    "
    done
    if [[ " ${claim_types[*]} " =~ [[:space:]]${MPM_CLAIM_TYPE}[[:space:]] ]]; then
      local attachment_path=$(mktemp)
      fetch_file "${fbucket}" "${subject_hash}" "${attachment_path}"
      # A very rough way to parse a proto, but good enough for a demo.
      local parsed=$(strings "${attachment_path}")
      [[ "${parsed}" =~ ([a-z/_]+) ]] && pkg_name=${BASH_REMATCH[0]} || exit 2
      [[ "${parsed}" =~ ([0-9a-f_-]{46}) ]] && version_id=${BASH_REMATCH[0]} || exit 2
      echo -e "    MPM package name:    ${PURPLE}${pkg_name}${COLOFF}"
      echo -e "    MPM package version: ${PURPLE}${version_id}${COLOFF}"
    fi
  done
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
    --key_file)
      shift
      keyfile="$1"
      shift
      list_all_endorsements "${fbucket}" "${ibucket}" "${keyfile}"
      ;;
    *)
      usage_and_exit
      ;;
  esac
done
