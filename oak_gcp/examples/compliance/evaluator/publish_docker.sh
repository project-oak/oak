#!/bin/bash
#
# Copyright 2026 The Project Oak Authors
#
# Publishes the Compliance Evaluator container image to Google Artifact Registry.
#
# Usage:
#   ./publish_docker.sh <PROJECT_ID> <REPOSITORY_NAME>

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

if [ "$#" -lt 2 ]; then
  echo "Usage: $0 <PROJECT_ID> <REPOSITORY_NAME>"
  exit 1
fi

PROJECT_ID="$1"
REPOSITORY_NAME="$2"
IMAGE_NAME="compliance-evaluator"
IMAGE_URL="europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/${IMAGE_NAME}:latest"

docker build --tag="${IMAGE_URL}" .
docker push "${IMAGE_URL}"

echo ""
echo "Evaluator container published to: ${IMAGE_URL}"
echo "Image SHA256 digest:"
docker inspect --format='{{index .RepoDigests 0}}' "${IMAGE_URL}"
