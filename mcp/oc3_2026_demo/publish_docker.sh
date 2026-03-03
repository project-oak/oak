#!/bin/bash

# Publishes the Oak Functions MCP server container image to an Artifact Registry.
#
# Usage:
#   ./publish_docker.sh <PROJECT_ID> <REPOSITORY_NAME>
#
# Example:
#   ./publish_docker.sh my-gcp-project my-artifact-registry-repo
#
# Prerequisites:
#   - gcloud CLI authenticated (`gcloud auth login`)
#   - Docker configured for Artifact Registry (`gcloud auth configure-docker europe-west1-docker.pkg.dev`)
#   - Bazel available (run within `nix develop` if using the Oak Nix environment)

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

if [ "$#" -lt 2 ]; then
  echo "Usage: $0 <PROJECT_ID> <REPOSITORY_NAME>"
  echo "  PROJECT_ID:      Your GCP project ID"
  echo "  REPOSITORY_NAME: Your Artifact Registry repository name"
  exit 1
fi

PROJECT_ID="$1"
REPOSITORY_NAME="$2"
IMAGE_NAME="oak-functions-mcp"
IMAGE_URL="europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/${IMAGE_NAME}:latest"

# Build Docker image.
bazel run //mcp/oak_functions_mcp:oak_functions_mcp_server_load_image

# Publish Docker image.
docker tag "${IMAGE_NAME}":latest "${IMAGE_URL}"
docker push "${IMAGE_URL}"

echo ""
echo "Oak Functions MCP Server container image is available at:"
echo "  ${IMAGE_URL}"
echo ""
echo "To get the image digest (SHA), run:"
echo "  docker inspect --format='{{index .RepoDigests 0}}' ${IMAGE_URL}"
