#!/bin/bash

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

IMAGE_NAME="private-agent"
PROJECT_ID="oak-examples-477357"
REPOSITORY_NAME="private-agent"
IMAGE_URL="us-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/${IMAGE_NAME}:latest"

# Pin Python dependencies.
# pip-compile requirements.in --generate-hashes -o requirements.txt

# Build Docker image.
docker build --tag=${IMAGE_URL} .

# Publish Docker image.
docker push ${IMAGE_URL}

echo "Private Agent container image is available on ${IMAGE_URL}"
