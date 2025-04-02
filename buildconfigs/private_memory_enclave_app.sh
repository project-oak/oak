#!/bin/bash
#
# Build configuration for private_memory_enclave_bundle.tar.
#
export PACKAGE_NAME=private_memory_enclave_app

export BUILD_COMMAND=(
  nix
  develop
  .#githubBuildShell
  --command
  just
  private_memory_enclave_bundle
)

export SUBJECT_PATHS=(
  artifacts/private_memory_enclave_bundle.tar
)
