#!/bin/bash

# Exit immediately if a command exits with a non-zero status.
set -e

# Define workspace root, crate directory, and output directory.
readonly WORKSPACE_ROOT=$(bazel info workspace)
readonly CRATE_DIR=oak_containers_examples/hello_world/web_client
readonly OUTPUT_DIR=${CRATE_DIR}/pkg

# Navigate to the Bazel workspace root.
cd "$WORKSPACE_ROOT"

# Build the project using wasm-pack.
echo "INFO: Building the project using wasm-pack"
(cd "${CRATE_DIR}" && wasm-pack build --target web)

# Copy index.html to the output directory.
echo "INFO: Copying index.html to the output directory: ${OUTPUT_DIR}"
cp "${CRATE_DIR}/index.html" "${OUTPUT_DIR}"

# Start a HTTP server in the output directory.
echo "INFO: Starting a HTTP server in the output directory: ${OUTPUT_DIR}"
(cd "${OUTPUT_DIR}" && npx servor)
