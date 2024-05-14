#!/bin/bash
#
# Build configuration for oak_containers_stage1.
#
export PACKAGE_NAME=oak_containers_stage1

export BUILD_COMMAND=(
  nix
  develop
  .#stage1Provenance
  --command
  env
  --chdir=oak_containers_stage1
  make
)

export BINARY_PATH=target/stage1.cpio
export SUBJECT_PATH="${BINARY_PATH}"
