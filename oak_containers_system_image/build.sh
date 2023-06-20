#!/bin/bash

docker build . --tag oak-containers-system-image
# We need to actually create a container, otherwise we won't be able to use `docker export` that gives us a filesystem image.
# (`docker save` creates a tarball which has all the layers separate, which is _not_ what we want.)
readonly NEW_DOCKER_CONTAINER_ID="$(docker create oak-containers-system-image:latest)"

mkdir -p target
docker export "$NEW_DOCKER_CONTAINER_ID" > target/image.tar

docker rm "$NEW_DOCKER_CONTAINER_ID"
