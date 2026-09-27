#!/bin/bash

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

IMAGE_NAME="oak-functions-mcp"
PROJECT_ID="${1:-oak-examples-477357}"
REPOSITORY_NAME="${2:-oak-trusted-agent}"
IMAGE_URL="us-east5-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/mcp/server:latest"

# Build Docker image.
bazel run //oak_trusted_agent/mcp/server:oak_functions_mcp_server_load_image

# Publish Docker image.
docker tag ${IMAGE_NAME}:latest ${IMAGE_URL}
docker push ${IMAGE_URL}

echo "Oak Functions MCP Server container image is available on ${IMAGE_URL}"
