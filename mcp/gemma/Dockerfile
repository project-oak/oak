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

# Copy the Oak Proxy binary and the config file from the build context.
COPY bin/oak_proxy_server /usr/local/bin/oak_proxy_server
COPY oak_proxy_server.toml /etc/oak_proxy_server.toml

# Run Oak Proxy that terminates the Oak Session and redirects HTTP requests to
# Ollama.
ENTRYPOINT [ \
    "/usr/local/bin/oak_proxy_server", \
    "--config=/etc/oak_proxy_server.toml" \
]
