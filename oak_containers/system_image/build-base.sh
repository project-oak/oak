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

cp --force "$LINUX_KERNEL_SOURCE" target/linux-"$LINUX_KERNEL_VERSION".tar.xz
cp --force "$LINUX_KERNEL_CONFIG" target/minimal.config

function build_base {
  local tag=$1
  local dockerfile=$2
  local tar_name=$3

  docker buildx build . \
   --build-arg LINUX_KERNEL_VERSION="$LINUX_KERNEL_VERSION" \
   --tag="$tag":latest \
   --file "$dockerfile"

  # We need to actually create a container, otherwise we won't be able to use
  # `docker export` that gives us a filesystem image.
  # (`docker save` creates a tarball which has all the layers separate, which is
  # _not_ what we want.)
  local NEW_DOCKER_CONTAINER_ID="$(docker create "$tag":latest)"

  # We export a plain tarball.
  # The oak_containers_sysimage_base oci_image rule will use this tarball to
  # create an OCI image that it can then push to Google artifact registry.
  # There *might* be a better approach here, but this is working for now.
  docker export "$NEW_DOCKER_CONTAINER_ID" > target/"$tar_name"
  docker rm "$NEW_DOCKER_CONTAINER_ID"

  # Repackage the base image tar so that entries are in a consistent order and have a
  # consistent mtime. fakeroot ensures that file permissions are maintained, even
  # when not building as root.
  #
  # Note that it's necessary to overwrite `/etc/hosts` because Docker always
  # produces an empty file, which means `localhost` won't resolve. Performing the
  # copy in this step (vs appending to the tar) ensures that the file permissions
  # don't change -- regardless of the permissions of `files/etc/hosts`.
  sandbox="$(mktemp -d)"
  fakeroot -- sh -c "\
    tar --extract --file target/$tar_name --directory \"${sandbox}\" \
    && cp files/etc/hosts \"${sandbox}/etc/hosts\" \
    && tar --create --sort=name --file target/$tar_name --mtime='2000-01-01Z' \
      --numeric-owner --directory \"${sandbox}\" ."
  rm -rf -- "$sandbox"
}

function build_vanilla_base {
  build_base "oak-containers-sysimage-base" "base_image.Dockerfile" "base-image.tar"

}

function build_nvidia_base {
  build_base "oak-containers-sysimage-nvidia-base" "nvidia_base_image.Dockerfile" "nvidia-base-image.tar"
}

if [ -z "${1:-}" ]
then
  set +o xtrace
  echo ""
  echo "Building both vanilla and nvidia base images."
  echo ""
  echo "If you want to build just one of the base image types, use:"
  echo "./scripts/build-bash.sh vanilla"
  echo "or"
  echo "./scripts/build-bash.sh nvidia"
  echo ""
  sleep 1
  set -o xtrace
  build_vanilla_base
  build_nvidia_base
elif [ "$1" == "vanilla" ]
then
  build_vanilla_base
elif [ "$1" == "nvidia" ]
then
  build_nvidia_base
fi

set +o xtrace
printf "\n\nIf you want to push this newly created base, run:\n"
printf "\nbazel run oak_containers/system_image:push_base\n"
printf "(and/or) bazel run oak_containers/system_image:push_nvidia_base\n\n"
printf "If you want to use the newly created base, update the hash for\n"
printf "the oak_containers_sysimage_base oci_pull target (or the nvidia flavour\n"
printf "if needed) in WORKSPACE\n\n"
