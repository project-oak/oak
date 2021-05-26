#!/usr/bin/env bash

readonly EXPERIMENTAL_SCRIPTS_DIR="$(dirname "$0")"
# shellcheck source=experimental/oak_functions_with_envoy/scripts/common.sh
source "$EXPERIMENTAL_SCRIPTS_DIR/common.sh"

# Build Oak Functions server binary, and the `weather_lookup` example application built on Oak Functions.
./scripts/docker_run ./scripts/runner run-functions-examples \
  --example-name=weather_lookup \
  --run-server=false \
  --client-variant=none

# Copy binaries to `experimental` directory, because global `.dockerignore` ignores all the files.
readonly EXPERIMENTAL_BIN=./experimental/oak_functions_with_envoy/bin
mkdir --parents "${EXPERIMENTAL_BIN}"
cp ./oak_functions/loader/target/x86_64-unknown-linux-musl/release/oak_functions_loader "${EXPERIMENTAL_BIN}"
cp ./oak_functions/examples/weather_lookup/config.toml "${EXPERIMENTAL_BIN}"
cp ./oak_functions/examples/weather_lookup/bin/weather_lookup.wasm "${EXPERIMENTAL_BIN}"

docker build \
  --file="./experimental/oak_functions_with_envoy/client/client.Dockerfile" \
  --tag="${ENVOY_CLIENT_IMAGE_NAME}:latest" \
  ./experimental/oak_functions_with_envoy

docker build \
  --file="./experimental/oak_functions_with_envoy/server/server.Dockerfile" \
  --tag="${ENVOY_SERVER_IMAGE_NAME}:latest" \
  ./experimental/oak_functions_with_envoy
