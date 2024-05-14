#!/bin/bash
#
# Build configuration for oak_containers_system_image.
#
export PACKAGE_NAME=oak_containers_system_image

export BUILD_COMMAND=(
  nix
  develop
  .#systemImageProvenance
  --command
  just
  oak_containers_system_image
)

export BINARY_PATH=oak_containers_system_image/target/image.tar.xz
export SUBJECT_PATH="${BINARY_PATH}"
