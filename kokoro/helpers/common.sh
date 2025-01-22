#!/usr/bin/env bash

# Detect the kokoro job type, so our scripts can make configuration decisions
# based on whether we are running in presubmit or continous mode.
#
# The Kokoro-specific variable is translated into a a more generic version, so
# that we don't leak Kokoro details outside of this directory.
#
# Information on Kokoro Job variables:
# https://g3doc.corp.google.com/devtools/kokoro/g3doc/platforms/configs/containers/win2019-java_config.md#dynamic-variables
readonly KOKORO_JOB_TYPE="${KOKORO_ROOT_JOB_TYPE:-}"

if [ "$KOKORO_JOB_TYPE" == "PRESUBMIT_GERRIT_ON_BORG" ]; then
  export CI_JOB_TYPE="PRESUBMIT"
elif [ "$KOKORO_JOB_TYPE" == "CONTINUOUS_INTEGRATION" ]; then
  export CI_JOB_TYPE="CONTINUOUS"
else
  export CI_JOB_TYPE="LOCAL"
fi

export RUST_BACKTRACE=1
export RUST_LOG=debug
export XDG_RUNTIME_DIR=/var/run
export JUST_TIMESTAMP=true
export JUST_TIMESTAMP_FORMAT='JUST:%H:%M:%S%.3f'

function kokoro_cleanup() {
    # Clean up bazel out directories to avoid everything being considered an action output.
    # That is also problematic because bazel-out is an absolute symlink, and that is not allowed by
    # RBE. See b/357487334.
    rm --recursive --force \
      ./bazel-bin \
      ./bazel-out \
      ./bazel-testlogs \
      ./bazel-workspace \
      ./codelab/bazel-out \
      ./codelab/bazel-bin \
      ./codelab/bazel-testlogs \
      ./codelab/bazel-codelab \
      ./bazel/test_workspace/bazel-bin \
      ./bazel/test_workspace/bazel-out \
      ./bazel/test_workspace/bazel-testlogs \
      ./bazel/test_workspace/bazel-test_workspace
}
