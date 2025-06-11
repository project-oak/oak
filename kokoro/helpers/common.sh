#!/usr/bin/env bash

function configure_common_env() {
  export RUST_BACKTRACE=1
  export RUST_LOG=debug
  export XDG_RUNTIME_DIR=/var/run
  export JUST_TIMESTAMP=true
  export JUST_TIMESTAMP_FORMAT='JUST:%H:%M:%S%.3f'
}

function configure_bazelrc() {
  JOB_TYPE=${KOKORO_JOB_TYPE:-local}
  if [ "$JOB_TYPE" == "SUB_JOB" ]
  then
    JOB_TYPE=${KOKORO_ROOT_JOB_TYPE:-local}
  fi

  echo "Using JOB_TYPE: ${JOB_TYPE}"

  if [ "$JOB_TYPE" == "PRESUBMIT_GERRIT_ON_BORG" ]; then
    echo "build --config=unsafe-fast-presubmit" >> ./.tmp.ci.bazelrc
  elif [ "$JOB_TYPE" == "CONTINUOUS_INTEGRATION" ]; then
    echo "build --config=ci" >> ./.tmp.ci.bazelrc
  else
    touch ./.tmp.ci.bazelrc
  fi
  trap "rm --force ./.tmp.ci.bazelrc" EXIT
}
