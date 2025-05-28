#!/bin/bash
#
# Build configuration for oak_containers_orchestrator.
#
export PACKAGE_NAME=oak_containers_orchestrator

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-oak_containers_orchestrator
)

export SUBJECT_PATHS=(
  artifacts/binaries/oak_containers_orchestrator
)
