#!/bin/bash

### Build the base system image with Docker.
### This script is expected to be run manually, and infrequently, for now.
### It only needs to be run if base_image.Dockerfile changes.

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

readonly SCRIPTS_DIR="$(dirname "$0")"

cd "$SCRIPTS_DIR"

mkdir --parent target

# Fix the file permissions that will be loaded into the system image, as Git doesn't track them.
# Unfortunately we can't do it in Dockerfile (with `COPY --chown`), as that requires BuildKit.
chmod --recursive a+rX files

docker build . --tag=oak-containers-sysimage-base:latest --file base_image.Dockerfile

# We need to actually create a container, otherwise we won't be able to use
# `docker export` that gives us a filesystem image.
# (`docker save` creates a tarball which has all the layers separate, which is
# _not_ what we want.)
readonly NEW_DOCKER_CONTAINER_ID="$(docker create oak-containers-sysimage-base:latest)"

# We export a plain tarball.
# The oak_containers_sysimage_base oci_image rule will use this tarball to
# create an OCI image that it can then push to Google artifact registry.
# There *might* be a better approach here, but this is working for now.
docker export "$NEW_DOCKER_CONTAINER_ID" > target/base-image.tar

docker rm "$NEW_DOCKER_CONTAINER_ID"

# Hack, as Docker doesn't give us a `/etc/hosts` which means `localhost` won't resolve.
tar --append --file=target/base-image.tar --directory=files etc/hosts

set +o xtrace
printf "\n\nIf you want to push this newly created base, run:\n"
printf "\nbazel run oak_containers_system_image:push_base\n\n"
printf "If you want to use the newly created base, update the hash for\n"
printf "the oak_containers_sysimage_base oci_pull target in WORKSPACE\n\n"
