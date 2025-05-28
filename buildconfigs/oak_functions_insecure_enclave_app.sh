#!/bin/bash
#
# Build configuration for oak_functions_insecure_enclave_app.
#
export PACKAGE_NAME=oak_functions_insecure_enclave_app

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-oak_functions_insecure_enclave_app
)

export SUBJECT_PATHS=(
  artifacts/binaries/oak_functions_insecure_enclave_app
)
