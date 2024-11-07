#!/bin/bash
#
# Build configuration for oak_containers_nvidiasystem_image.
#
export PACKAGE_NAME=oak_containers_nvidia_system_image

export BUILD_COMMAND=(
  nix
  develop
  .#systemImageShell
  --command
  just
  oak_containers_nvidia_system_image
)

export SUBJECT_PATHS=(
  artifacts/oak_containers_nvidia_system_image.tar.xz
)
