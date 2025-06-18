#!/usr/bin/env bash

function configure_common_env() {
  export RUST_BACKTRACE=1
  export RUST_LOG=debug
  export XDG_RUNTIME_DIR=/var/run
  export JUST_TIMESTAMP=true
  export JUST_TIMESTAMP_FORMAT='JUST:%H:%M:%S%.3f'
}

function _install_tmp_bazelrc() {
  readonly B=./.tmp.ci.bazelrc
  local contents="$1"
  if [[ -f ${B} ]]; then
    local actual=$(cat "${B}")
    if [[ "${actual}" != "${contents}" ]]; then
      >&2 echo "Failed precondition: Read ${actual}, expected ${contents}"
      exit 1
    fi
  else
    echo "${contents}" > "${B}"
    >&2 echo "Installed ${B} with \"${contents}\""
    # shellcheck disable=SC2064
    trap "rm --force ${B}" EXIT
  fi
}

function configure_bazelrc() {
  JOB_TYPE=${KOKORO_JOB_TYPE:-local}
  if [ "$JOB_TYPE" == "SUB_JOB" ]; then
    JOB_TYPE=${KOKORO_ROOT_JOB_TYPE:-local}
  fi

  echo "Using JOB_TYPE: ${JOB_TYPE}"

  if [ "$JOB_TYPE" == "PRESUBMIT_GERRIT_ON_BORG" ]; then
    _install_tmp_bazelrc "build --config=unsafe-fast-presubmit"
  elif [ "$JOB_TYPE" == "CONTINUOUS_INTEGRATION" ]; then
    _install_tmp_bazelrc "build --config=ci"
  else
    _install_tmp_bazelrc ""
  fi
}
