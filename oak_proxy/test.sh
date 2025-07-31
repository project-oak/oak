#!/bin/bash

set -e
set -x

export RUST_LOG=debug

# Create TOML config files
cat > client.toml <<EOF
listen_address = "127.0.0.1:9090"
server_proxy_url = "ws://127.0.0.1:8081"
attestation_generators = []
attestation_verifiers = []
EOF

cat > server.toml <<EOF
listen_address = "127.0.0.1:8081"
backend_address = "127.0.0.1:8080"
attestation_generators = []
attestation_verifiers = []
EOF

# Start the backend server
nc -l 127.0.0.1 8080 > >(tee backend_output.txt) &
BACKEND_PID=$!
# Give it a moment to start up
sleep 1

# The binaries are available in the runfiles directory.
# Their path is relative to the workspace root.
SERVER_PROXY_BIN="./oak_proxy/server/server"
CLIENT_PROXY_BIN="./oak_proxy/client/client"

# Start the server proxy
echo "Starting server proxy..."
$SERVER_PROXY_BIN --config server.toml > >(tee server_output.txt) 2>&1 &
SERVER_PID=$!
# Wait for the server to start
sleep 2

# Start the client proxy
echo "Starting client proxy..."
$CLIENT_PROXY_BIN --config client.toml > >(tee client_output.txt) 2>&1 &
CLIENT_PID=$!
# Wait for the client to start
sleep 2

# Send a message, waiting for 20s after send so that the keep-alive is sent
echo "Sending message..."
echo "Hello, proxy!" | nc -w 20 127.0.0.1 9090

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