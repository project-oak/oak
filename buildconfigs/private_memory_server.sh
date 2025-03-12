#!/bin/bash
#
# Build configuration for private_memory_server.
#
export PACKAGE_NAME=private_memory_server

export BUILD_COMMAND=(
  nix
  develop
  .#githubBuildShell
  --command
  just
  oak_private_memory
)

export SUBJECT_PATHS=(
  artifacts/private_memory_server
)
