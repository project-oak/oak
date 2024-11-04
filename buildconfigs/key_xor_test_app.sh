#!/bin/bash
#
# Build configuration for key_xor_test_app.
#
export PACKAGE_NAME=key_xor_test_app

export BUILD_COMMAND=(
  nix
  develop
  .#bazelRustShell
  --command
  just
  build_key_xor_test_app
)

export SUBJECT_PATHS=(
  artifacts/enclave_apps/key_xor_test_app
)
