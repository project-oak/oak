#!/bin/bash
#
# Build configuration for oak_restricted_kernel_tdx_virtio_console_channel.
#
# Verify changes to this file by running:
#   scripts/test_buildconfigs \
#   buildconfigs/oak_restricted_kernel_tdx_virtio_console_channel.sh
export PACKAGE_NAME=oak_restricted_kernel_tdx_virtio_console_channel

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github oak_restricted_kernel_wrapper_tdx_virtio_console_channel
)

# The first element must be the Transparent Release binary (the main binary).
export SUBJECT_PATHS=(
  artifacts/binaries/oak_restricted_kernel_tdx_virtio_console_channel
  artifacts/subjects/oak_restricted_kernel_wrapper_tdx_virtio_console_channel_measurement_image
  artifacts/subjects/oak_restricted_kernel_wrapper_tdx_virtio_console_channel_measurement_setup_data
)
