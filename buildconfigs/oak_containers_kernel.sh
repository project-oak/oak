#!/bin/bash
#
# Build configuration for oak_containers_kernel.
#
# TODO: b/333745447 - Replace this file with its counterparts in ./buildconfigs_full_provenance.
export PACKAGE_NAME=oak_containers_kernel

export BUILD_COMMAND=(
  nix
  develop
  .#bzImageProvenance
  --command
  env
  --chdir=oak_containers_kernel
  make
)

export BINARY_PATH=oak_containers_kernel/target/bzImage
export SUBJECT_PATH="${BINARY_PATH}"
