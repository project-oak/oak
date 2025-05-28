#!/bin/bash
#
# Build configuration for private_memory_server.
#
export PACKAGE_NAME=private_memory_server

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-private_memory_server
)

export SUBJECT_PATHS=(
  artifacts/binaries/private_memory_server
)
