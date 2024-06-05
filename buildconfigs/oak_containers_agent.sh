#!/bin/bash
#
# Build configuration for oak_containers_agent.
#
export PACKAGE_NAME=oak_containers_agent

export BUILD_COMMAND=(
  nix
  develop
  .#systemImageProvenance
  --command
  just
  oak_containers_agent
)

export SUBJECT_PATHS=(
  oak_containers_agent/target/oak_containers_agent_patched
)
