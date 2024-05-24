#!/bin/bash
#
# Build configuration for oak_restricted_kernel_simple_io_init_rd_wrapper_bin.
#
export PACKAGE_NAME=oak_restricted_kernel_simple_io_init_rd_wrapper_bin

export BUILD_COMMAND=(
  nix
  develop
  .#rust
  --command
  just
  oak_restricted_kernel_simple_io_init_rd_wrapper
)

# The first element must be the Transparent Release binary (the main binary).
export SUBJECT_PATHS=(
  oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_simple_io_init_rd_wrapper_bin
  oak_restricted_kernel_wrapper/bin/oak_restricted_kernel_simple_io_init_rd/subjects/oak_restricted_kernel_simple_io_init_rd_image
  oak_restricted_kernel_wrapper/bin/oak_restricted_kernel_simple_io_init_rd/subjects/oak_restricted_kernel_simple_io_init_rd_setup_data
)
