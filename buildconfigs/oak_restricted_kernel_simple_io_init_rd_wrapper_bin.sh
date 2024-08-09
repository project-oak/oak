#!/bin/bash
#
# Build configuration for oak_restricted_kernel_simple_io_init_rd_wrapper_bin.
#
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
  oak_restricted_kernel_wrapper/bin/wrapper_bzimage_simple_io_channel
  oak_restricted_kernel_wrapper/bin/wrapper_simple_io_channel_subjects/oak_restricted_kernel_simple_io_channel_image
  oak_restricted_kernel_wrapper/bin/wrapper_simple_io_channel_subjects/oak_restricted_kernel_simple_io_channel_setup_data
)
