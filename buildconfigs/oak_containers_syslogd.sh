#!/bin/bash
#
# Build configuration for oak_containers_syslogd.
#
export PACKAGE_NAME=oak_containers_syslogd

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-oak_containers_syslogd
)

export SUBJECT_PATHS=(
  artifacts/binaries/oak_containers_syslogd
)
