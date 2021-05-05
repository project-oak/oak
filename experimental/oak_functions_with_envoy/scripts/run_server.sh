#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

echo Running server proxy
/usr/local/bin/envoy --config-path /server.yaml -- --alsologtostderr &
# Give slack time for Envoy proxy to start in the background.
sleep 1

echo Running Oak Functions
/oak_functions_loader \
    --http-listen-port=8081 \
    --wasm-path=/module.wasm \
    --config-path=/config.toml
echo Oak Functions exited with $?
