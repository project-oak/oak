# Use Envoy Proxy 1.19.0-dev.
FROM envoyproxy/envoy-dev:22825906e35c1d61b495f7b5f2517249cc56f77d

RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  curl \
  netcat-openbsd \
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

COPY client/client.yaml /etc/envoy/client.yaml
COPY client/client_localhost.yaml /etc/envoy/client_localhost.yaml
COPY scripts/run_client.sh /etc/envoy/run_client.sh

ENTRYPOINT ["/etc/envoy/run_client.sh"]
