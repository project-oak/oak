#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

echo Running client proxy
if [[ "${1:-}" == localhost ]]; then
    # Dedicated `--base-id` is needed to run multiple Envoy proxies on the same machine:
    # https://github.com/envoyproxy/envoy/issues/88
    /usr/local/bin/envoy --config-path /client_localhost.yaml --base-id 1 -- --alsologtostderr &
else
    /usr/local/bin/envoy --config-path /client.yaml -- --alsologtostderr &
fi
# Give slack time for Envoy proxy to start in the background.
sleep 1

# Test request coordinates are defined in `oak_functions/lookup_data_generator/src/data.rs`.
echo Running HTTP client
curl \
  --fail \
  --fail-early \
  --http2 \
  --http2-prior-knowledge \
  --request POST \
  --data '{"lat":0,"lng":0}' \
  --location \
  --verbose \
  --output - \
  --include \
  localhost:8000/invoke
