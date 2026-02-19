#!/bin/bash
# Helper functions for runner commands.

# Run a command, capture stderr separately, along with the combined stderr/stdout.
function run_command_with_logfiles() {
  local -r stderr_log="${1}"
  local -r combined_log="${2}"
  local -r command="${3}"

  # What is this doing?
  # &> (Redirect stdout + stderr)
  # >(tee f) To a tee process writing to f
  # 2> (Redirect stderr)
  # >(tee f >2) To a tee process writing to f, but keeping the output of tee only on stderr.
  eval "${command}" > >(tee "${combined_log}") 2> >(tee "${stderr_log}" >&2)
}

# Run a command, and then generate simple junit XML files so it can feel like a test.
function run_as_test_case() {
  local -r name="${1}"
  local -r command="${2}"

  local -r logdir="artifacts/subtask-logs/${name}"
  mkdir --parents "${logdir}"
  local -r stderr_log="${logdir}/stderr.log"
  local -r combined_log="${logdir}/sponge_log.log"

  # Reset the special bash SECONDS variable so we can time the command.
  SECONDS=0
  if ! run_command_with_logfiles "${stderr_log}" "${combined_log}" "${command}"; then
    # Seconds will have counted the number of seconds since it was reset.
    local -r time=${SECONDS}
    echo "${name} FAILED"
    emit_test_fail "${name}" "${stderr_log}" "${time}"
    return 1
  else
    # Seconds will have counted the number of seconds since it was reset.
    local -r time=${SECONDS}
    echo "${name} PASSED"
    emit_test_pass "${name}" "${combined_log}" "${time}"
  fi
}

function emit_test_pass() {
  local -r xmlfile="artifacts/subtask-logs/${1}/sponge_log.xml"

  export NAME="${1}"
  export LOG=$(tail -c 100000 "${2}")
  export TIME="${3}"
  envsubst <kokoro/helpers/test_pass.xml.tpl >"${xmlfile}"
}

function emit_test_fail() {
  local -r xmlfile="artifacts/subtask-logs/${1}/sponge_log.xml"

  export NAME="${1}"
  # Try to find only relevant lines to show in the main failure log.
  export FAILURE=$(grep -C 100 "\(fail\|error\)" "${2}" | tail -c 100000)
  export TIME="${3}"
  envsubst <kokoro/helpers/test_failure.xml.tpl >"${xmlfile}"
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
