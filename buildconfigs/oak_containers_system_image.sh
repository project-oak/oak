#!/bin/bash
#
# Build configuration for oak_containers_system_image.
#
export PACKAGE_NAME=oak_containers_system_image

export BUILD_COMMAND=(
  nix
  develop
  .#githubBuildShell
  --command
  just
  oak_containers_system_image
)

export SUBJECT_PATHS=(
  artifacts/oak_containers_system_image.tar.xz
)
