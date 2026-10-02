#!/bin/bash
#
# Copyright 2026 The Project Oak Authors
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

# Cryptographically verifies a downloaded evaluation bundle (in-toto statement,
# artifact digest, and Confidential Space attestation token) in a local
# directory.
#
# Usage:
#   ./oak_trusted_agent/demo/model/verify.sh [dir]

set -euo pipefail

readonly OUT_DIR="${1:-/tmp/trusted_eval}"
readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
readonly IMAGE_REPO="us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/eval/gemma4-31b-it-qat"
readonly INDEX_JSON="${REPO_ROOT}/bazel-bin/oak_trusted_agent/eval/image_gemma4_31b_it_qat/index.json"
readonly DEFAULT_IMAGE_DIGEST="sha256:0b0d5ef834a6c06bd59697ebdb1c16421fb8ff8fc3541cb714f93d7cfd747528"

if [[ -n "${EXPECTED_IMAGE_DIGEST:-}" ]]; then
  IMAGE_DIGEST="${EXPECTED_IMAGE_DIGEST}"
elif [[ -f "${INDEX_JSON}" ]]; then
  IMAGE_DIGEST="$(jq -r '.manifests[0].digest' "${INDEX_JSON}")"
else
  IMAGE_DIGEST="${DEFAULT_IMAGE_DIGEST}"
fi

cd "${REPO_ROOT}"
bazel run --config=release --ui_event_filters=-info,-stderr --noshow_progress \
  //oak_trusted_agent/provenance/verifier:oak_trusted_agent_provenance_verifier -- \
  --statement="${OUT_DIR}/signed.json" \
  --subject="report.jsonl=${OUT_DIR}/report.jsonl" \
  --unchecked-subject=gemma4:31b-it-qat \
  --expected-image-prefix="${IMAGE_REPO}" \
  --expected-image-digest="${IMAGE_DIGEST}" \
  --expected-predicate-type=https://project-oak.github.io/oak/trusted_agent/eval/v1
