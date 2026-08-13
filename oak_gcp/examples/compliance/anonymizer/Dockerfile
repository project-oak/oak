# Stage 1: Load oak-proxy.
FROM us-west1-docker.pkg.dev/oak-examples-477357/oak-proxy/oak-proxy@sha256:9543d12e9653e39cd642ab48dbb7cf0488cb5696c678bf8ee2528c523638bb1b as oak_proxy

# Stage 2: Builder.
FROM python:3.12-slim as builder

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONHASHSEED=42

RUN python -m venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"

WORKDIR /builder
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Stage 3: Final Confidential Space image.
FROM python:3.12-slim as final

RUN useradd --create-home user
USER user
WORKDIR /home/user

COPY --chown=user:user --from=builder /opt/venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"

COPY --chown=user:user server.py ./
COPY --chown=user:user proxy_server.toml /etc/proxy_server.toml
COPY --chown=user:user --from=oak_proxy /bin/server /bin/oak_proxy_server

ENV RUST_LOG=info
EXPOSE 8080

LABEL "tee.launch_policy.allow_env_override"="CONTAINER_IMAGE"
LABEL "tee.launch_policy.log_redirect"="always"

ENTRYPOINT ["/bin/oak_proxy_server", "--config=/etc/proxy_server.toml"]
