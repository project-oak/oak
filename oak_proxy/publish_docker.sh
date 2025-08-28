#!/bin/bash

IMAGE_NAME="oak-proxy"
PROJECT_ID="oak-examples-477357"
REPOSITORY_NAME="oak-proxy"
IMAGE_URL="europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/${IMAGE_NAME}:latest"

# Build Docker image.
bazel build //oak_proxy:oak_proxy_load_image
bazel-bin/oak_proxy/oak_proxy_load_image.sh

# Publish Docker image.
docker tag ${IMAGE_NAME}:latest ${IMAGE_URL}
docker push ${IMAGE_URL}

echo "Oak Proxy container image is available on ${IMAGE_URL}"
