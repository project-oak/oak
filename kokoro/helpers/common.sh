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
    if [[ ${actual} != "${contents}" ]]; then
      >&2 echo "Failed precondition: Read ${actual}, expected ${contents}"
      exit 1
    fi
  else
    echo "${contents}" >"${B}"
    >&2 echo "Installed ${B} with \"${contents}\""
    # shellcheck disable=SC2064
    trap "rm --force ${B}" EXIT
  fi
}

function configure_bazelrc() {
  # Kokoro will populate this for us.
  JOB_TYPE=${KOKORO_JOB_TYPE:-local}

  # If we are using job grouping, this may be a child job.
  # So we can get the actual type from a different env variable.
  if [ "${JOB_TYPE}" == "SUB_JOB" ]; then
    JOB_TYPE=${KOKORO_ROOT_JOB_TYPE:-local}
  fi

  echo "Using JOB_TYPE: ${JOB_TYPE}"

  # Create the .tmp.ci.bazelrc that selects the desired configuration for the
  # given job type. This configuration controls things like logging style and
  # remote cache usage.
  # See .ci.bazelrc for more details.
  if [ "${JOB_TYPE}" == "PRESUBMIT_GERRIT_ON_BORG" ]; then
    _install_tmp_bazelrc "build --config=unsafe-fast-presubmit"
  elif [ "${JOB_TYPE}" == "CONTINUOUS_INTEGRATION" ]; then
    _install_tmp_bazelrc "build --config=ci"
  else
    _install_tmp_bazelrc ""
  fi
}

function collect_test_logs {
  mkdir --parents artifacts/bazel-testlogs

  # Copy all test.log and test.xml for the most recent bazel test run into our artifacts directory.
  fd "^test.log$" "bazel-testlogs" \
    --threads=1 --exec cp --parents --force --preserve=timestamps \
    {} artifacts
  fd "^test.xml$" "bazel-testlogs" \
    --threads=1 --exec cp --parents --force --preserve=timestamps \
    {} artifacts

  # Rename the files to the name that will let them be parsed as sponge logs.
  fd "^test.log" artifacts/bazel-testlogs --exec mv {} "{//}/sponge_log.log"
  fd "^test.xml" artifacts/bazel-testlogs --exec mv {} "{//}/sponge_log.xml"
}

# ── Timing helpers ──────────────────────────────────────────────────────────
# Records how long each step takes and prints a summary at the end.
#
# Usage:
#   time_step "step name" command arg1 arg2 ...
#   print_timing_summary

_STEP_NAMES=()
_STEP_DURATIONS=()

# Runs a command, records its wall-clock duration under the given label, and
# propagates the command's exit status.
# The first argument is a string label for the step, and the remaining arguments
# are the command to execute with all of its arguments.
function time_step() {
  local label="$1"
  shift

  echo "[$(date --utc)] -- START: ${label} --"
  # Reset the special bash SECONDS variable
  SECONDS=0
  local rc=0
  # The remaining arguments are the command to execute.
  "$@" || rc=$?

  # Capture the SECONDS variable after running the command.
  local elapsed_seconds=${SECONDS}

  _STEP_NAMES+=("${label}")
  _STEP_DURATIONS+=("${elapsed_seconds}")

  local minutes=$(( elapsed_seconds / 60 ))
  local seconds=$(( elapsed_seconds % 60 ))
  local status="OK"
  if (( rc != 0 )); then
    status="FAIL (exit ${rc})"
  fi
  echo "[$(date --utc)] -- END: ${label} -- ${minutes}m${seconds}s -- ${status} --"

  return "${rc}"
}

# Records a step whose start time is known. Calculates duration, prints progress,
# and registers the step.
# Usage:
#   record_start_time "step name" start_epoch_seconds
function record_start_time() {
  local label="$1"
  local start_epoch="${2:-}"

  if [[ -n "${start_epoch}" ]]; then
    local duration=$(( EPOCHSECONDS - start_epoch ))
    echo "[$(date --utc)] ${label}: ${duration}s"
    _STEP_NAMES+=("${label}")
    _STEP_DURATIONS+=("${duration}")
  fi
}

# Prints a table of all recorded step durations.
function print_timing_summary() {
  # Disable command tracing to keep the timing summary clean.
  # `local -` localizes the shell options ($-) to this function, so
  # disabling tracing (set +x) is automatically restored on function exit.
  local -
  set +x

  echo ""
  echo "+--------------------------------------------------+-----------+"
  echo "|                   TIMING SUMMARY                             |"
  echo "+--------------------------------------------------+-----------+"

  local total=0
  for i in "${!_STEP_NAMES[@]}"; do
    local name="${_STEP_NAMES[$i]}"
    local dur="${_STEP_DURATIONS[$i]}"
    total=$(( total + dur ))
    local m=$(( dur / 60 ))
    local s=$(( dur % 60 ))
    printf "| %-48s | %4dm %02ds |\n" "${name}" "${m}" "${s}"
  done

  echo "+--------------------------------------------------+-----------+"
  local tm=$(( total / 60 ))
  local ts=$(( total % 60 ))
  printf "| %-48s | %4dm %02ds |\n" "TOTAL" "${tm}" "${ts}"
  echo "+--------------------------------------------------+-----------+"
  echo ""
}

