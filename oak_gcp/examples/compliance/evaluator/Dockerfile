ARG BASE_IMAGE=europe-west1-docker.pkg.dev/octo-aif-sandbox/compliance-enclaves/attested-model-base:latest

# Stage 1: Load oak-proxy.
FROM us-west1-docker.pkg.dev/oak-examples-477357/oak-proxy/oak-proxy@sha256:9543d12e9653e39cd642ab48dbb7cf0488cb5696c678bf8ee2528c523638bb1b as oak_proxy

# Stage 2: Final Confidential Space image.
FROM ${BASE_IMAGE} as final

# hadolint ignore=DL3002
USER root

# Install Python and clean up apt cache
RUN apt-get update && apt-get install -y --no-install-recommends python3 python3-pip python3-venv curl && rm -rf /var/lib/apt/lists/*

RUN python3 -m venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"

WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY server.py llm_manager.py ./
COPY proxy_server.toml /etc/proxy_server.toml

COPY --from=oak_proxy /bin/server /bin/oak_proxy_server

ARG OLLAMA_MODEL=gemma4:e4b
ENV OLLAMA_MODEL=${OLLAMA_MODEL}
ENV OLLAMA_NUM_CTX=8192
ENV RUST_LOG=info
EXPOSE 8080

LABEL "tee.launch_policy.allow_env_override"="CONTAINER_IMAGE,OLLAMA_MODEL,OLLAMA_URL,OLLAMA_NUM_CTX"
LABEL "tee.launch_policy.log_redirect"="always"

ENTRYPOINT ["/bin/oak_proxy_server", "--config=/etc/proxy_server.toml"]


