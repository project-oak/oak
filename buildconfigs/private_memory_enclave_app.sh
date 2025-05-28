#!/bin/bash
#
# Build configuration for private_memory_enclave_bundle.tar.
#
export PACKAGE_NAME=private_memory_enclave_app

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-private_memory_enclave_app
)

export SUBJECT_PATHS=(
  artifacts/binaries/private_memory_enclave_bundle.tar
)
