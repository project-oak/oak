#!/bin/bash

IMAGE_NAME="attested-gemma"
PROJECT_ID="oak-examples-477357"
REPOSITORY_NAME="attested-gemma"
IMAGE_URL="europe-west1-docker.pkg.dev/${PROJECT_ID}/${REPOSITORY_NAME}/${IMAGE_NAME}:latest"

# Build Docker image.
docker build --tag=${IMAGE_NAME}:latest .

# Publish Docker image.
docker tag ${IMAGE_NAME}:latest ${IMAGE_URL}
docker push ${IMAGE_URL}

echo "Oak Proxy container image is available on ${IMAGE_URL}"
