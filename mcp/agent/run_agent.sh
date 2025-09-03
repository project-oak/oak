#!/bin/bash

# Script that runs Oak Proxy Server (that runs the Agent server), and also runs
# 2 instances of the Oak Proxy Client that connect to Gemma and an MCP server.
#
# TODO: b/435400315 - Refactor Oak Proxy to run both server and clients.

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

# Start the proxy server in the background.
/bin/oak_proxy_server --config=/etc/proxy_server.toml &

# Start the MCP proxy client in the background.
/bin/oak_proxy_client --config=/etc/mcp_proxy_client.toml &

# Start the Gemma proxy client in the background.
/bin/oak_proxy_client --config=/etc/gemma_proxy_client.toml &

# Wait for all background processes to exit.
wait
