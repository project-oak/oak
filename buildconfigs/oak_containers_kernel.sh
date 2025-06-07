#!/bin/bash
#
# Build configuration for oak_containers_kernel.
#
export PACKAGE_NAME=oak_containers_kernel

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-oak_containers_kernel
)

# The first element must be the Transparent Release binary (the main binary).
export SUBJECT_PATHS=(
  artifacts/binaries/oak_containers_kernel
  artifacts/subjects/oak_containers_kernel/oak_containers_kernel_image
  artifacts/subjects/oak_containers_kernel/oak_containers_kernel_setup_data
)
