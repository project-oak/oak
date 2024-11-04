#!/bin/bash
#
# Build configuration for oak_orchestrator.
#
export PACKAGE_NAME=oak_orchestrator

export BUILD_COMMAND=(
  nix
  develop
  .#rust
  --command
  just
  build_enclave_app
  oak_orchestrator
)

export SUBJECT_PATHS=(
  artifacts/enclave_apps/oak_orchestrator
)
