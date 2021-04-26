#!/usr/bin/env bash

readonly EXPERIMENAL_SCRIPTS_DIR="$(dirname "$0")"
source "$EXPERIMENAL_SCRIPTS_DIR/common.sh"

docker build \
  --file="./experimental/envoy_proxy/client/client.Dockerfile" \
  --tag="${ENVOY_CLIENT_IMAGE_NAME}:latest" \
  ./experimental/envoy_proxy

docker build \
  --file="./experimental/envoy_proxy/server/server.Dockerfile" \
  --tag="${ENVOY_SERVER_IMAGE_NAME}:latest" \
  ./experimental/envoy_proxy
