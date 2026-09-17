#!/bin/bash
#
# Copyright 2026 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the 'License');
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an 'AS IS' BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

set -o errexit
set -o nounset
set -o pipefail

BENCHMARK="${BENCHMARK:-hello_world}"
OUT_DIR="${OUT_DIR:-/out}"

# Start Ollama in the background and verify it stays alive until ready.
/bin/ollama serve &
OLLAMA_PID=$!
until ollama list >/dev/null 2>&1; do
  kill -0 "${OLLAMA_PID}" 2>/dev/null || {
    echo "Ollama exited prematurely" >&2
    exit 1
  }
  sleep 1
done

ARGS=(
  "--benchmark=${BENCHMARK}"
  "--model=${OLLAMA_MODEL}"
  "--out-dir=${OUT_DIR}"
)
if [[ ${NO_ATTESTATION:-false} == "true" ]]; then
  ARGS+=("--no-attestation")
fi
if [[ -n ${RESULTS_BUCKET:-} ]]; then
  ARGS+=("--upload-to=gs://${RESULTS_BUCKET}/model-eval")
fi

python3 -m harness.run "${ARGS[@]}"
