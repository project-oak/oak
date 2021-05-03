#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

echo Running client proxy
# Dedicated `--base-id` is needed to run multiple Envoy proxies on the same machine:
# https://github.com/envoyproxy/envoy/issues/88
/envoy --config-path /client.yaml --base-id 1 -- --alsologtostderr &
# Give slack time for Envoy proxy to start in the background.
sleep 1

echo Running HTTP client
curl \
  --fail \
  --fail-early \
  --http2 \
  --http2-prior-knowledge \
  --request POST \
  --data '{"lat":51,"lon":0}' \
  --location \
  --verbose \
  localhost:8080
