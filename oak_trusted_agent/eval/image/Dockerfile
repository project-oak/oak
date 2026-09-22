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

# TODO: b/429197818 - Switch container image build to Bazel.
FROM ollama/ollama:0.34.1@sha256:0c0a83210471fb50226bcdc2d6611d20ab13ae87e024cc304c94a6a5765c5e65

# Bind Ollama to loopback so it is unreachable outside the container.
ENV OLLAMA_HOST=127.0.0.1:11434 \
    OLLAMA_DEBUG=false \
    OLLAMA_KEEP_ALIVE=-1

# Bake model weights into the image layer first so APT/Python changes do not invalidate the weights cache.
ARG MODEL=gemma4
ARG MODEL_PARAMS=e2b-it-qat
ARG MODELS_DIR=/models
ENV OLLAMA_MODELS=${MODELS_DIR} \
    OLLAMA_MODEL=${MODEL}:${MODEL_PARAMS}

RUN /bin/ollama serve & \
    until ollama list >/dev/null 2>&1; do sleep 1; done && \
    ollama pull ${MODEL}:${MODEL_PARAMS}

# Verify the manifest digest to pin the exact model weights at build time.
ARG MODEL_SHA256SUM=07ea59a474013479c8b6b802bef095c40e964a1d776ba02f264c0e30e1aede0c
RUN bash -o pipefail -c 'echo "${MODEL_SHA256SUM}  ${MODELS_DIR}/manifests/registry.ollama.ai/library/${MODEL}/${MODEL_PARAMS}" | sha256sum --check'

# Install Python for the evaluation harness.
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    python3 \
    python3-pip \
    python3-venv \
    && rm -rf /var/lib/apt/lists/*

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONHASHSEED=42

RUN python3 -m venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"

WORKDIR /workspace
COPY requirements.txt .
RUN pip install --no-cache-dir --require-hashes -r requirements.txt

COPY image/bin/signer /bin/signer
COPY image/entrypoint.sh /bin/entrypoint.sh
COPY harness ./harness
COPY benchmarks ./benchmarks

# Omit allow_cmd_override so callers cannot sign arbitrary commands under this image digest.
LABEL "tee.launch_policy.allow_env_override"="CONTAINER_IMAGE,BENCHMARK,RESULTS_BUCKET"
LABEL "tee.launch_policy.log_redirect"="always"

ENTRYPOINT ["/bin/entrypoint.sh"]
