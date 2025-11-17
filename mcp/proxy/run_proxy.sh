#!/bin/bash

# Starts the Oak Proxy client, connecting to the server proxy using the URL
# provided via the `SERVER_PROXY_URL`` environment variable.
#
# TODO: b/435400315 - Refactor Oak Proxy to run both server and clients.

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

/bin/oak_proxy_client --config=/etc/proxy_client.toml --server-proxy-url="${SERVER_PROXY_URL}"
