#!/bin/bash
#
# Build configuration for oak_restricted_kernel_virtio_console_init_rd_wrapper_bin.
#
# Verify changes to this file by running:
#   scripts/test_buildconfigs \
#   buildconfigs/oak_restricted_kernel_virtio_console_init_rd_wrapper_bin.sh
export PACKAGE_NAME=oak_restricted_kernel_virtio_console_init_rd_wrapper_bin

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github oak_restricted_kernel_wrapper_virtio_console_channel
)

# The first element must be the Transparent Release binary (the main binary).
export SUBJECT_PATHS=(
  artifacts/binaries/oak_restricted_kernel_virtio_console_init_rd_wrapper_bin
  artifacts/subjects/oak_restricted_kernel_wrapper_virtio_console_channel_measurement_image
  artifacts/subjects/oak_restricted_kernel_wrapper_virtio_console_channel_measurement_setup_data
)
