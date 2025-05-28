#!/bin/bash
#
# Build configuration for oak_containers_stage1.
#
export PACKAGE_NAME=oak_containers_stage1

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-stage1_cpio
)

export SUBJECT_PATHS=(
  artifacts/binaries/stage1.cpio
)
