#!/bin/bash

# Exit immediately if a command exits with a non-zero status
set -e

readonly WORKSPACE_ROOT=$(bazel info workspace)
readonly OUTPUT_DIR=oak_attestation_explain_wasm/pkg

# Navigating to the Bazel workspace root
cd "$WORKSPACE_ROOT"

echo "INFO: Building the project using wasm-pack"
just oak_attestation_explain_wasm

echo "INFO: Copying index.html to the output directory: ${OUTPUT_DIR}"
cp oak_attestation_explain_wasm/index.html "${OUTPUT_DIR}"

echo "INFO: Starting a HTTP server in the output directory: ${OUTPUT_DIR}"
python3 -m http.server --directory "${OUTPUT_DIR}" 0
