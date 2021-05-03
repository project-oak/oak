#!/usr/bin/env bash

readonly EXPERIMENAL_SCRIPTS_DIR="$(dirname "$0")"
# shellcheck source=experimental/envoy_proxy/scripts/common.sh
source "$EXPERIMENAL_SCRIPTS_DIR/common.sh"

# TODO(#1943): Remove when #1943 is submitted.
cargo build --target=x86_64-unknown-linux-musl \
  --manifest-path=./oak_functions/loader/Cargo.toml \
  --release

# Build the `weather_lookup` example application built on Oak Functions.
cargo -Zunstable-options build --release \
  --target=wasm32-unknown-unknown \
  --manifest-path=./oak_functions/examples/weather_lookup/module/Cargo.toml \
  --out-dir=./oak_functions/examples/weather_lookup/bin

docker build \
  --file="./experimental/envoy_proxy/client/client.Dockerfile" \
  --tag="${ENVOY_CLIENT_IMAGE_NAME}:latest" \
  .

docker build \
  --file="./experimental/envoy_proxy/server/server.Dockerfile" \
  --tag="${ENVOY_SERVER_IMAGE_NAME}:latest" \
  ./experimental/envoy_proxy
