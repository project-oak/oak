#!/bin/bash
#
# Build configuration for oak_restricted_kernel_simple_io_init_rd_wrapper_bin.
#
# TODO: b/333745447 - Replace this file with its counterparts in ./buildconfigs_full_provenance.
export PACKAGE_NAME=oak_restricted_kernel_simple_io_init_rd_wrapper_bin

export BUILD_COMMAND=(
  nix
  develop
  .#rust
  --command
  just
  oak_restricted_kernel_simple_io_init_rd_wrapper
)

export BINARY_PATH=oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_simple_io_init_rd_wrapper_bin
export SUBJECT_PATH="${BINARY_PATH}"
