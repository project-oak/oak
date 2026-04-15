#!/bin/bash
#
# Build configuration for endorscope_cli.
#
export PACKAGE_NAME=endorscope_cli

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github endorscope_cli
)

export SUBJECT_PATHS=(
  artifacts/binaries/endorscope_cli
)
