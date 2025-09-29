# Stage 1: Load oak-proxy.
FROM us-west1-docker.pkg.dev/oak-examples-477357/oak-proxy/oak-proxy@sha256:9543d12e9653e39cd642ab48dbb7cf0488cb5696c678bf8ee2528c523638bb1b as oak_proxy

# Stage 2: Main image.
FROM ollama/ollama:0.11.6@sha256:1868fd51253099b8f48b89b981e5d8ba23e4db161a501b86e29593071c1c069b

# Reduce logging verbosity.
ENV OLLAMA_DEBUG=false

# Never unload model weights from the GPU.
ENV OLLAMA_KEEP_ALIVE=-1

# Allow all origins.
ENV OLLAMA_ORIGINS=*

# Start a temporary Ollama server and save the model weights in /models.
# This Docker image uses Ollama to run GPT-OSS model.
# <https://huggingface.co/openai/gpt-oss-20b>
ARG MODEL=gpt-oss
ARG MODEL_PARAMS=20b
ARG MODELS_DIR=/models
ENV OLLAMA_MODELS=${MODELS_DIR}
RUN /bin/ollama serve & sleep 5 && ollama pull ${MODEL}:${MODEL_PARAMS}

# The model digest can be extracted from the model card.
#
# 1) First run the Ollama Docker and expose the default port:
# ```bash
# docker run -p 11434:11434 ollama/ollama:latest
# ```
#
# 2) Then run Python in a separate terminal and execute the following code:
# ```python
# import ollama
# ollama.pull('gpt-oss:20b') # This will take some time.
# models = ollama.list().models
# print(models[0]['digest'])
# ```
ARG MODEL_SHA256SUM=aa4295ac10c3afb60e6d711289fc6896f5aef82258997b9efdaed6d0cc4cd8b8

# Verify the digest of the downloaded model.
# Currently we are only verifying the digest of a model manifest, i.e. an Ollama
# specific file that contains digests of all model related files stored in the
# Ollama repository.
RUN bash -o pipefail -c 'echo "${MODEL_SHA256SUM} ${MODELS_DIR}/manifests/registry.ollama.ai/library/${MODEL}/${MODEL_PARAMS}" | sha256sum --check'

# Copy the Oak Proxy binary from the first stage and the config file from the
# build context.
COPY --from=oak_proxy /bin/server /bin/oak_proxy_server
COPY oak_proxy_server.toml /etc/proxy.toml

# Enable logging for Oak Proxy.
# This doesn't log the underlying secure communication.
ENV RUST_LOG=info

# Expose the port Oak Proxy is listening on.
EXPOSE 8080

# https://cloud.google.com/confidential-computing/confidential-space/docs/create-customize-workloads#launch_policies
LABEL "tee.launch_policy.allow_env_override"="CONTAINER_IMAGE"
LABEL "tee.launch_policy.log_redirect"="always"

# Run Oak Proxy that terminates the Oak Session and redirects HTTP requests to
# Ollama.
ENTRYPOINT [ \
    "/bin/oak_proxy_server", \
    "--config=/etc/proxy.toml" \
]
