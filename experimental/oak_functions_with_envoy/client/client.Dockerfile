# Use Envoy Proxy 1.19.0-dev.
FROM envoyproxy/envoy-dev:22825906e35c1d61b495f7b5f2517249cc56f77d

RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  curl \
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

COPY ./client/client.yaml /client.yaml
COPY ./client/client_localhost.yaml /client_localhost.yaml
COPY ./scripts/run_client.sh /run_client.sh

ENTRYPOINT ["/run_client.sh"]
