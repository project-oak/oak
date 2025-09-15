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
echo "Running Oak Proxy server for the Agent"
/bin/oak_proxy_server --config=/etc/proxy_server.toml &

# Start the Gemma proxy client in the background.
echo "Running Oak Proxy client for Gemma: ${GEMMA_PROXY_URL}"
/bin/oak_proxy_client --config=/etc/gemma_proxy_client.toml --server-proxy-url "${GEMMA_PROXY_URL}" &

# Start the MCP proxy client in the background.
echo "Running Oak Proxy client for MCP Server: ${MCP_PROXY_URL}"
/bin/oak_proxy_client --config=/etc/mcp_proxy_client.toml --server-proxy-url "${MCP_PROXY_URL}" &

# Wait for all background processes to exit.
wait
