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

# Builds and pushes the reproducible gemma4:31b-it-qat evaluation image, runs a
# benchmark on an NVIDIA H100 inside Confidential Space, waits for the signed
# result bundle in GCS, and tears down the H100 VM on exit.
#
# Usage:
#   ./oak_trusted_agent/demo/model/run.sh [agentdojo|hello_world]

set -euo pipefail

readonly BENCHMARK="${1:-agentdojo}"
readonly BENCHMARK_SLUG="${BENCHMARK//_/-}"
readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly REPO_ROOT="$(cd "${SCRIPT_DIR}/../../.." && pwd)"
readonly TF_DIR="${REPO_ROOT}/oak_trusted_agent/eval/terraform"
readonly IMAGE_REPO="us-east5-docker.pkg.dev/oak-examples-477357/oak-trusted-agent/eval/gemma4-31b-it-qat"
readonly GCS_PREFIX="gs://oak-trusted-agent/eval/gemma4-31b-it-qat/${BENCHMARK_SLUG}"

cd "${REPO_ROOT}"

echo "==> Building and pushing //oak_trusted_agent/eval:push_gemma4_31b_it_qat..."
bazel run --config=release //oak_trusted_agent/eval:push_gemma4_31b_it_qat

readonly DIGEST="$(jq -r '.manifests[0].digest' "${REPO_ROOT}/bazel-bin/oak_trusted_agent/eval/image_gemma4_31b_it_qat/index.json")"
echo "==> Image digest: ${DIGEST}"

# Clear any previous signed.json at this prefix so the poll loop waits for the
# newly uploaded bundle from this run.
gcloud storage rm "${GCS_PREFIX}/signed.json" 2>/dev/null || true

terraform -chdir="${TF_DIR}" init -input=false

cleanup() {
  echo "==> Destroying Confidential Space H100 VM..."
  terraform -chdir="${TF_DIR}" destroy -auto-approve \
    -var-file="${SCRIPT_DIR}/terraform.tfvars"
}
trap cleanup EXIT

echo "==> Provisioning Confidential Space H100 VM for benchmark '${BENCHMARK}'..."
terraform -chdir="${TF_DIR}" apply -auto-approve \
  -var-file="${SCRIPT_DIR}/terraform.tfvars" \
  -var="benchmark=${BENCHMARK}" \
  -var="image_digest=${IMAGE_REPO}@${DIGEST}"

echo "==> Waiting for signed evaluation bundle at ${GCS_PREFIX}/signed.json..."
for ((i = 1; i <= 900; i++)); do
  if gcloud storage ls "${GCS_PREFIX}/signed.json" >/dev/null 2>&1; then
    echo "==> Evaluation complete! Bundle uploaded to ${GCS_PREFIX}/"
    gcloud storage ls -l "${GCS_PREFIX}/"
    exit 0
  fi
  sleep 10
done

echo "ERROR: Timed out waiting for ${GCS_PREFIX}/signed.json" >&2
exit 1
