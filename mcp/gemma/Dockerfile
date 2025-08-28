# Stage 1: Load oak-proxy.
FROM europe-west1-docker.pkg.dev/oak-examples-477357/oak-proxy/oak-proxy@sha256:9def78165d90bb2bb5a7d5d05a4498611595a76c218255eaed6487372789fd15 as oak_proxy

# Stage 2: Main image.
FROM ollama/ollama:0.11.6

# Reduce logging verbosity.
ENV OLLAMA_DEBUG=false

# Never unload model weights from the GPU.
ENV OLLAMA_KEEP_ALIVE=-1

# Allow all origins.
ENV OLLAMA_ORIGINS=*

# Start a temporary Ollama server and save the model weights in /models.
ARG MODEL=gemma:2b
ARG MODELS_DIR=/models
ENV OLLAMA_MODELS=${MODELS_DIR}
RUN /bin/ollama serve & sleep 5 && ollama pull ${MODEL}

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
# ollama.pull('gemma:2b') # This will take some time.
# models = ollama.list().models
# print(models[0]['digest'])
# ```
ARG MODEL_SHA256SUM=b50d6c999e592ae4f79acae23b4feaefbdfceaa7cd366df2610e3072c052a160

# Verify the digest of the downloaded model.
# Currently we are only verifying the digest of a model manifest, i.e. an Ollama
# specific file that contains digests of all model related files stored in the
# Ollama repository.
RUN bash -o pipefail -c 'echo "${MODEL_SHA256SUM} ${MODELS_DIR}/manifests/registry.ollama.ai/library/gemma/2b" | sha256sum --check'

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
