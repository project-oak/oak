#!/bin/bash
#
# Build configuration for oak_containers_kernel.
#
export PACKAGE_NAME=oak_containers_kernel

export BUILD_COMMAND=(
  nix
  develop
  .#bzImageProvenance
  --command
  just
  oak_containers_kernel
)

# The first element must be the Transparent Release binary (the main binary).
export SUBJECT_PATHS=(
  oak_containers_kernel/target/bzImage
  oak_containers_kernel/bin/subjects/oak_containers_kernel_image
  oak_containers_kernel/bin/subjects/oak_containers_kernel_setup_data
)
