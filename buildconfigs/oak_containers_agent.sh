#!/bin/bash
#
# Build configuration for oak_containers_agent.
#
export PACKAGE_NAME=oak_containers_agent

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-oak_containers_agent
)

export SUBJECT_PATHS=(
  artifacts/binaries/oak_containers_agent
)
