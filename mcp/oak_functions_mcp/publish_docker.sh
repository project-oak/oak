#!/bin/bash

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

IMAGE_NAME="oak-functions-mcp"
PROJECT_ID="oak-functions-standalone"
REPOSITORY_NAME="oak-functions-mcp-containers"
IMAGE_URL="europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/${IMAGE_NAME}:latest"

# Build Docker image.
bazel run //mcp/oak_functions_mcp:oak_functions_mcp_server_load_image

# Publish Docker image.
docker tag ${IMAGE_NAME}:latest ${IMAGE_URL}
docker push ${IMAGE_URL}

echo "Oak Functions MCP Server container image is available on ${IMAGE_URL}"
