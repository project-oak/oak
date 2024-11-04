#!/bin/bash
#
# Build configuration for oak_functions_enclave_app.
#
export PACKAGE_NAME=oak_functions_enclave_app

export BUILD_COMMAND=(
  nix
  develop
  .#rust
  --command
  just
  build_enclave_app
  oak_functions_enclave_app
)

export SUBJECT_PATHS=(
  artifacts/enclave_apps/oak_functions_enclave_app
)
