#!/bin/bash

IMAGE_NAME="attested-mcp-server"
PROJECT_ID="oak-examples-477357"
REPOSITORY_NAME="attested-mcp-server"
IMAGE_URL="europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/${IMAGE_NAME}:latest"

# Build Docker image.
bazel build //mcp/server:mcp_server_load_image
bazel-bin/mcp/server/mcp_server_load_image.sh

# Publish Docker image.
docker tag ${IMAGE_NAME}:latest ${IMAGE_URL}
docker push ${IMAGE_URL}

echo "MCP Server container image is available on ${IMAGE_URL}"
