#!/bin/bash
#
# Build configuration for oak_containers_syslogd.
#
export PACKAGE_NAME=oak_containers_syslogd

export BUILD_COMMAND=(
  nix
  develop
  .#githubBuildShell
  --command
  just
  oak_containers_syslogd
)

export SUBJECT_PATHS=(
  artifacts/oak_containers_syslogd
)
