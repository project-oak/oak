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
  env
  --chdir=enclave_apps/oak_orchestrator
  cargo
  build
  --release
)

export BINARY_PATH=enclave_apps/target/x86_64-unknown-none/release/oak_orchestrator
export SUBJECT_PATH="${BINARY_PATH}"
