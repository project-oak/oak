#!/bin/bash
#
# Build configuration for oak_echo_raw_enclave_app.
#
export PACKAGE_NAME=oak_echo_raw_enclave_app

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-oak_echo_raw_enclave_app
)

export SUBJECT_PATHS=(
  artifacts/binaries/oak_echo_raw_enclave_app
)
