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

# Downloads a published evaluation bundle (report.jsonl, predicate.json, and
# signed.json) from GCS into a local directory.
#
# Usage:
#   ./oak_trusted_agent/demo/model/get.sh [dir] [agentdojo|hello_world]

set -euo pipefail

readonly OUT_DIR="${1:-/tmp/trusted_eval}"
readonly BENCHMARK="${2:-agentdojo}"
readonly BENCHMARK_SLUG="${BENCHMARK//_/-}"
readonly GCS_PREFIX="gs://oak-trusted-agent/eval/gemma4-31b-it-qat/${BENCHMARK_SLUG}"

rm -rf "${OUT_DIR}"
mkdir -p "${OUT_DIR}"

echo "==> Downloading signed evaluation bundle from ${GCS_PREFIX} to ${OUT_DIR}..."
gcloud storage cp "${GCS_PREFIX}/*" "${OUT_DIR}/"
