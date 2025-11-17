# Stage 1: Load oak-proxy.
FROM us-west1-docker.pkg.dev/oak-examples-477357/oak-proxy/oak-proxy@sha256:9543d12e9653e39cd642ab48dbb7cf0488cb5696c678bf8ee2528c523638bb1b as oak_proxy

# Stage 2: Final image.
FROM debian:12-slim@sha256:78d2f66e0fec9e5a39fb2c72ea5e052b548df75602b5215ed01a17171529f706 as final

# Install libssl3, which is a dependency for oak_proxy_client.
# Also clean up apt lists to reduce image size.
RUN apt-get update && \
    apt-get install -y --no-install-recommends libssl3 && \
    rm -rf /var/lib/apt/lists/*

# Create a non-root user.
RUN useradd --create-home user
USER user
WORKDIR /home/user

# Copy the Oak Proxy binaries from the first stage.
COPY --chown=user:user --from=oak_proxy /bin/client /bin/oak_proxy_client

# Copy Oak Proxy config files.
COPY --chown=user:user config/proxy_client.toml /etc/proxy_client.toml

# Copy the proxy bash script.
COPY --chown=user:user run_proxy.sh /home/user/run_proxy.sh

# Enable logging for Oak Proxy.
ENV RUST_LOG=info

# Expose the port Oak Proxy is listening on.
EXPOSE 8080

# Confidential Space launch policy that allows specific environment variables to
# be provided at runtime:
# - `SERVER_PROXY_URL` is known at runtime because it is dynamically assigned
#    by gCloud to corresponding services.
#
# https://cloud.google.com/confidential-computing/confidential-space/docs/create-customize-workloads#launch_policies
LABEL "tee.launch_policy.allow_env_override"="SERVER_PROXY_URL"
LABEL "tee.launch_policy.log_redirect"="always"

ENTRYPOINT ["/home/user/run_proxy.sh"]
