#!/bin/bash
#
# Build configuration for stage0_bin_tdx.
#
export PACKAGE_NAME=stage0_bin_tdx

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-stage0_bin_tdx
)

export SUBJECT_PATHS=(
  artifacts/binaries/stage0_bin_tdx
)
