#!/bin/bash
#
# Build configuration for oak_orchestrator.
#
export PACKAGE_NAME=oak_orchestrator

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-oak_orchestrator
)

export SUBJECT_PATHS=(
  artifacts/binaries/oak_orchestrator
)
