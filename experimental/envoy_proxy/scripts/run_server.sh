#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

echo Running server proxy
/usr/local/bin/envoy -c /etc/envoy/server.yaml -- --alsologtostderr &
# Give slack time for Envoy proxy to start in the background.
sleep 1

echo Running HTTP server
python3 -m http.server 8081
echo HTTP server exited with $?
