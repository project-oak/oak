#!/bin/bash

set -e
set -x

# Start the backend server
nc -l 127.0.0.1 8080 > backend_output.txt &
BACKEND_PID=$!
# Give it a moment to start up
sleep 1

# The binaries are available in the runfiles directory.
# Their path is relative to the workspace root.
SERVER_PROXY_BIN="./oak_proxy/server/server"
CLIENT_PROXY_BIN="./oak_proxy/client/client"

# Start the server proxy
echo "Starting server proxy..."
$SERVER_PROXY_BIN > server_output.txt 2>&1 &
SERVER_PID=$!
# Wait for the server to start
sleep 2

# Start the client proxy
echo "Starting client proxy..."
$CLIENT_PROXY_BIN > client_output.txt 2>&1 &
CLIENT_PID=$!
# Wait for the client to start
sleep 2

# Send a message
echo "Sending message..."
echo "Hello, proxy!" | nc -w 1 127.0.0.1 9090

# Wait for the message to be processed
sleep 2

# Kill the processes
echo "Cleaning up processes..."
kill $CLIENT_PID || true
kill $SERVER_PID || true
kill $BACKEND_PID || true
wait

# Check the output
echo "Checking output..."
if grep -q "Hello, proxy!" backend_output.txt; then
    echo "Test passed!"
    exit 0
else
    echo "Test failed! Backend output:"
    cat backend_output.txt
    echo "---"
    echo "Server output:"
    cat server_output.txt
    echo "---"
    echo "Client output:"
    cat client_output.txt
    exit 1
fi
