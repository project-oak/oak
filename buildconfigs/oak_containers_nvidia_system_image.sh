#!/bin/bash
#
# Build configuration for oak_containers_nvidiasystem_image.
#
export PACKAGE_NAME=oak_containers_nvidia_system_image

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-oak_containers_nvidia_system_image
)

export SUBJECT_PATHS=(
  artifacts/binaries/oak_containers_nvidia_system_image.tar.xz
)
