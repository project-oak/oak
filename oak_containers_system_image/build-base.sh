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

docker buildx build . --tag=oak-containers-sysimage-base:latest --file base_image.Dockerfile

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

# Repackage base-image.tar so that entries are in a consistent order and have a
# consistent mtime. fakeroot ensures that file permissions are maintained, even
# when not building as root.
#
# Note that it's necessary to overwrite `/etc/hosts` because Docker always
# produces an empty file, which means `localhost` won't resolve. Performing the
# copy in this step (vs appending to the tar) ensures that the file permissions
# don't change -- regardless of the permissions of `files/etc/hosts`.
sandbox="$(mktemp -d)"
fakeroot -- sh -c "\
  tar --extract --file target/base-image.tar --directory \"${sandbox}\" \
  && cp files/etc/hosts \"${sandbox}/etc/hosts\" \
  && tar --create --sort=name --file target/base-image.tar --mtime='2000-01-01Z' \
     --numeric-owner --directory \"${sandbox}\" ."
rm -rf -- "$sandbox"

set +o xtrace
printf "\n\nIf you want to push this newly created base, run:\n"
printf "\nbazel run oak_containers_system_image:push_base\n\n"
printf "If you want to use the newly created base, update the hash for\n"
printf "the oak_containers_sysimage_base oci_pull target in WORKSPACE\n\n"
