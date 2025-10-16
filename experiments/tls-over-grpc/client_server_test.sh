#!/bin/bash
set -o errexit
set -o nounset
set -o pipefail
set -o xtrace

SERVER_LOG=$(mktemp)
CLIENT_LOG=$(mktemp)

# Start the server in the background
"${SERVER}" --port=0 2>&1 | tee "${SERVER_LOG}" &
SERVER_PID=$!

# It can take a while for the server to start up.
# TODO(#5197): Figure out a way to wait for the server to be ready.
sleep 5

# Get the port the server is listening on.
SERVER_PORT=$(grep "Server listening on port" "${SERVER_LOG}" | awk '{print $NF}')

# Run the client
"${CLIENT}" --port="${SERVER_PORT}" 2>&1 | tee "${CLIENT_LOG}"

# Stop the server
kill "${SERVER_PID}"

grep "Received: Hello world" "${CLIENT_LOG}" || (echo "Client log did not contain expected output"; cat "${CLIENT_LOG}"; exit 1)
