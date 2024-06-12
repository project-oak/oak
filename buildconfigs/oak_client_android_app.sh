#!/bin/bash
#
# Build configuration for oak_client_android_app.
#
export PACKAGE_NAME=oak_client_android_app

export BUILD_COMMAND=(
  nix
  develop
  --command
  just
  oak_client_android_app
)

export SUBJECT_PATHS=(
  generated/client_app.apk
)
