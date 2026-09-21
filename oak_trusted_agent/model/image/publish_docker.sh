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

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
MODEL_DIR="$(cd "${SCRIPT_DIR}/.." && pwd)"
REPO_ROOT="$(cd "${MODEL_DIR}/../.." && pwd)"

PROJECT_ID="${1:-oak-examples-477357}"
REPOSITORY_NAME="${2:-oak-trusted-agent}"
MODEL_SLUG="${MODEL_SLUG:-gemma4-e2b-it-qat}"
IMAGE_NAME="model/${MODEL_SLUG}"
IMAGE_URL="us-east5-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/${IMAGE_NAME}:latest"

# Stage oak_proxy_server inside the build context because Docker cannot follow external symlinks.
trap 'rm -rf "${SCRIPT_DIR}/bin"' EXIT
mkdir -p "${SCRIPT_DIR}/bin"
PROXY_BIN="$(cd "${REPO_ROOT}" && bazel build --config=release //oak_proxy/server:server && bazel cquery --config=release --output=files //oak_proxy/server:server)"
install -m 0755 "${REPO_ROOT}/${PROXY_BIN}" "${SCRIPT_DIR}/bin/oak_proxy_server"

docker build --file="${SCRIPT_DIR}/Dockerfile" --tag="${IMAGE_URL}" "${MODEL_DIR}"

if [[ ${PUSH:-true} == "true" ]]; then
  docker push "${IMAGE_URL}"
  echo "Attested model container image is available on ${IMAGE_URL}"
  echo "Image SHA256 digest:"
  docker inspect --format='{{index .RepoDigests 0}}' "${IMAGE_URL}"
fi
