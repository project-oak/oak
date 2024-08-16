#!/bin/bash
#
# Build configuration for oak_restricted_kernel_simple_io_init_rd_wrapper_bin.
#
# Verify changes to this file by running:
#   scripts/test_buildconfigs \
#   buildconfigs/oak_restricted_kernel_simple_io_init_rd_wrapper_bin.sh
export PACKAGE_NAME=oak_restricted_kernel_simple_io_init_rd_wrapper_bin

export BUILD_COMMAND=(
  nix
  develop
  .#ci
  --command
  just
  oak_restricted_kernel_wrapper_simple_io_channel
)

# The first element must be the Transparent Release binary (the main binary).
export SUBJECT_PATHS=(
  generated/oak_restricted_kernel_wrapper_simple_io_channel_bin
  generated/oak_restricted_kernel_wrapper_simple_io_channel_measurement_image
  generated/oak_restricted_kernel_wrapper_simple_io_channel_measurement_setup_data
)
