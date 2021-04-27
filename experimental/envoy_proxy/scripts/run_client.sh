#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

echo Running client proxy
if [[ "${1:-}" == localhost ]]; then
    # Dedicated `--base-id` is needed to run multiple Envoy proxies on the same machine:
    # https://github.com/envoyproxy/envoy/issues/88
    /usr/local/bin/envoy --config-path /etc/envoy/client_localhost.yaml --base-id 1 -- --alsologtostderr &
else
    /usr/local/bin/envoy --config-path /etc/envoy/client.yaml -- --alsologtostderr &
fi
# Give slack time for Envoy proxy to start in the background.
sleep 1

echo Running HTTP client
curl --location --verbose localhost:8000
