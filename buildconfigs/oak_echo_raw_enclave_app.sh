#!/bin/bash
#
# Build configuration for oak_echo_raw_enclave_app.
#
export PACKAGE_NAME=oak_echo_raw_enclave_app

export BUILD_COMMAND=(
  nix
  develop
  .#bazelRustShell
  --command
  just
  build_enclave_app
  oak_echo_raw_enclave_app
)

export SUBJECT_PATHS=(
  artifacts/enclave_apps/oak_echo_raw_enclave_app
)
