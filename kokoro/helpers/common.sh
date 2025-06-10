#!/usr/bin/env bash

function configure_common_env() {
  export RUST_BACKTRACE=1
  export RUST_LOG=debug
  export XDG_RUNTIME_DIR=/var/run
  export JUST_TIMESTAMP=true
  export JUST_TIMESTAMP_FORMAT='JUST:%H:%M:%S%.3f'
}

function configure_bazelrc() {
  if [ "$KOKORO_ROOT_JOB_TYPE" == "PRESUBMIT_GERRIT_ON_BORG" ]; then
    echo "build --config=unsafe-fast-presubmit" >> ./.tmp.ci.bazelrc
  elif [ "$KOKORO_ROOT_JOB_TYPE" == "CONTINUOUS_INTEGRATION" ]; then
    echo "build --config=ci" >> ./.tmp.ci.bazelrc
  else
    touch ./.tmp.ci.bazelrc
  fi
  trap "rm --force ./.tmp.ci.bazelrc" EXIT
}
