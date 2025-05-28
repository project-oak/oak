#!/bin/bash
#
# Build configuration for oak_containers_stage1_tdx.
#
export PACKAGE_NAME=oak_containers_stage1_tdx

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-stage1_tdx_cpio
)

export SUBJECT_PATHS=(
  artifacts/binaries/stage1_tdx.cpio
)
