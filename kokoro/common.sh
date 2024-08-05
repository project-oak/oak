#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

export CI=kokoro
export RUST_BACKTRACE=1
export RUST_LOG=debug
export XDG_RUNTIME_DIR=/var/run
export JUST_TIMESTAMP=true
export JUST_TIMESTAMP_FORMAT='JUST:%H:%M:%S%.3f'

# Make sure we're in the root of the repository.
cd "$(dirname "$0")/.."

function kokoro_cleanup() {
    # Clean up bazel out directories to avoid everything being considered an action output.
    # That is also problematic because bazel-out is an absolute symlink, and that is not allowed by
    # RBE. See b/357487334.
    rm --recursive --force \
      ./bazel-bin \
      ./bazel-out \
      ./bazel-testlogs \
      ./bazel-workspace \
      ./bazel/test_workspace/bazel-bin \
      ./bazel/test_workspace/bazel-out \
      ./bazel/test_workspace/bazel-testlogs \
      ./bazel/test_workspace/bazel-test_workspace
}
