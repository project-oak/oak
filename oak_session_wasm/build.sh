#!/bin/bash

# Exit immediately if a command exits with a non-zero status.
set -e

# Define workspace root, crate directory, and output directory.
readonly WORKSPACE_ROOT=$(bazel info workspace)
readonly CRATE_DIR=oak_session_wasm

# Navigate to the Bazel workspace root.
cd "$WORKSPACE_ROOT"

# Build the project using wasm-pack.
echo "INFO: Building the project using wasm-pack"
(cd "${CRATE_DIR}" && wasm-pack build --target web)
