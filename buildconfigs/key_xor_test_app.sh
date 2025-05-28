#!/bin/bash
#
# Build configuration for key_xor_test_app.
#
export PACKAGE_NAME=key_xor_test_app

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-key_xor_test_app
)

export SUBJECT_PATHS=(
  artifacts/binaries/key_xor_test_app
)
