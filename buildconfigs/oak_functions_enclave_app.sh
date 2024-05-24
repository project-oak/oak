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
  env
  --chdir=enclave_apps/oak_functions_enclave_app
  cargo
  build
  --release
)

export SUBJECT_PATHS=(
  enclave_apps/target/x86_64-unknown-none/release/oak_functions_enclave_app
)
