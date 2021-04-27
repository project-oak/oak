# Use Envoy Proxy 1.19.0-dev.
FROM envoyproxy/envoy-dev:22825906e35c1d61b495f7b5f2517249cc56f77d

RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  python3 \
  netcat-openbsd \
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

COPY server/server.yaml /etc/envoy/server.yaml
COPY scripts/run_server.sh /etc/envoy/run_server.sh

ENTRYPOINT ["/etc/envoy/run_server.sh"]
