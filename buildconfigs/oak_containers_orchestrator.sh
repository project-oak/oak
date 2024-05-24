#!/bin/bash
#
# Build configuration for oak_containers_orchestrator.
#
export PACKAGE_NAME=oak_containers_orchestrator

export BUILD_COMMAND=(
  nix
  develop
  .#systemImageProvenance
  --command
  just
  oak_containers_orchestrator
)

export SUBJECT_PATHS=(
  oak_containers_orchestrator/target/oak_containers_orchestrator
)
