#!/bin/bash
#
# Build configuration for stage0_bin_tdx.
#
export PACKAGE_NAME=stage0_bin_tdx

export BUILD_COMMAND=(
  nix
  develop
  --command
  just
  stage0_bin_tdx
)

export SUBJECT_PATHS=(
  generated/stage0_bin_tdx
)
