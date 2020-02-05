#!/usr/bin/env bash

# Keep this in sync with /scripts/format.

readonly SCRIPTS_DIR="$(dirname "$(readlink -f "$0")")"
# shellcheck source=scripts/common
source "$SCRIPTS_DIR/common"


find . \
  \(  \
    -not \( -path ./bazel-cache -prune \) -and \
    -not \( -path ./cargo-cache -prune \) -and \
    -not \( -path ./examples/target -prune \) -and \
    -not \( -path ./oak/server/rust/target -prune \) -and \
    -not \( -path ./sdk/rust/target -prune \) -and \
    -not \( -path ./third_party -prune \) \
    \( -type f \( -name '*.rs' -o -name '*.cc' \) \) \
  \) -exec ./scripts/check_license {} +
