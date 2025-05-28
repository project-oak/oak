#!/bin/bash
#
# Build configuration for oak_client_android_app.
#
export PACKAGE_NAME=oak_client_android_app

export BUILD_COMMAND=(
  nix
  develop
  .#default
  --command
  just
  github-oak_client_android_app
)

export SUBJECT_PATHS=(
  artifacts/binaries/client_app.apk
)
