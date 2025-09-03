# Stage 1: Load oak-proxy.
FROM europe-west1-docker.pkg.dev/oak-examples-477357/oak-proxy/oak-proxy@sha256:b9fab154b5978fbb5149c5c9a98db6ceabdb965758a2078b66f8d6f1884ef922 as oak_proxy

# Stage 2: Builder.
# Digest can be accessed with the following command:
# ```bash
# docker pull python:3.12-slim
# docker inspect python:3.12-slim | jq -r '.[0].RepoDigests[0]'
# ```
# TODO: b/429197818 - Switch Agent build to Bazel.
FROM python:3.12-slim@sha256:d67a7b66b989ad6b6d6b10d428dcc5e0bfc3e5f88906e67d490c4d3daac57047 as builder

# Set PYTHONHASHSEED for deterministic builds within Python.
ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONHASHSEED=42

# Create and activate a virtual environment.
RUN python -m venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"

# Copy and install dependencies from the locked requirements file
WORKDIR /builder
COPY requirements.txt .
RUN pip install --no-cache-dir --require-hashes -r requirements.txt

# Stage 3: Final image.
# Use the same image as the builder.
FROM python:3.12-slim@sha256:d67a7b66b989ad6b6d6b10d428dcc5e0bfc3e5f88906e67d490c4d3daac57047 as final

# Create a non-root user.
RUN useradd --create-home user
USER user
WORKDIR /home/user

# Copy the virtual environment and application code from the builder stage.
COPY --chown=user:user --from=builder /opt/venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"

# Copy the agent code.
COPY --chown=user:user *.py ./

# Copy the Oak Proxy binaries from the first stage.
COPY --chown=user:user --from=oak_proxy /bin/server /bin/oak_proxy_server
COPY --chown=user:user --from=oak_proxy /bin/client /bin/oak_proxy_client

# Copy Oak Proxy config files.
COPY --chown=user:user proxy_server.toml /etc/proxy_server.toml
COPY --chown=user:user gemma_proxy_client.toml /etc/gemma_proxy_client.toml
COPY --chown=user:user mcp_proxy_client.toml /etc/mcp_proxy_client.toml

# Copy the agent bash script.
# TODO: b/435400315 - Refactor Oak Proxy to run both server and clients.
COPY --chown=user:user run_agent.sh /home/user/run_agent.sh

# Enable logging for Oak Proxy.
# This doesn't log the underlying secure communication.
ENV RUST_LOG=info

# Expose the port Oak Proxy is listening on.
EXPOSE 8080

# https://cloud.google.com/confidential-computing/confidential-space/docs/create-customize-workloads#launch_policies
LABEL "tee.launch_policy.allow_env_override"="CONTAINER_IMAGE"
LABEL "tee.launch_policy.log_redirect"="always"

# Run the agent.
ENTRYPOINT ["/home/user/run_agent.sh"]
