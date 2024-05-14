#!/bin/bash
#
# Build configuration for stage0_bin.
#
export PACKAGE_NAME=stage0_bin

export BUILD_COMMAND=(
  nix
  develop
  .#rust
  --command
  env
  --chdir=stage0_bin
  cargo
  objcopy
  --release
  --
  --output-target=binary
  target/x86_64-unknown-none/release/stage0_bin
)

export BINARY_PATH=stage0_bin/target/x86_64-unknown-none/release/stage0_bin
export SUBJECT_PATH="${BINARY_PATH}"
