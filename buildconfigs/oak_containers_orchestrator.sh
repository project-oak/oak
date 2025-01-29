#!/bin/bash
#
# Build configuration for oak_containers_orchestrator.
#
export PACKAGE_NAME=oak_containers_orchestrator

export BUILD_COMMAND=(
  nix
  develop
  .#githubBuildShell
  --command
  just
  oak_containers_orchestrator
)

export SUBJECT_PATHS=(
  artifacts/oak_containers_orchestrator
)
