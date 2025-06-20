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
    eval "${command}" &> >(tee "${combined_log}") 2> >(tee "${stderr_log}" >&2)
}

# Run a command, and then generate simple junit XML files so it can feel like a test.
function run_as_test_case() {
    local -r name="${1}"
    local -r command="${2}"

    local -r logdir="artifacts/subtask-logs/$name"
    mkdir --parents "${logdir}"
    local -r stdout_log="${logdir}/stdout.log"
    local -r stderr_log="${logdir}/stderr.log"
    local -r combined_log="${logdir}/sponge_log.log"

    if ! run_command_with_logfiles "${stderr_log}" "${combined_log}" "${command}"
    then
        echo "${name} FAILED"
        emit_test_fail "${name}" "${stderr_log}"
        failures+=("${name}")
    else
        echo "${name} PASSED"
        emit_test_pass "${name}" "${stdout_log}"
    fi
}

function emit_test_pass() {
    local -r xmlfile ="artifacts/subtask-logs/${1}/sponge_log.xml"

    export NAME="${1}"
    export LOG=$(cat "${2}")
    envsubst < kokoro/helpers/test_pass.xml.tpl > "${xmlfile}"
}

function emit_test_fail() {
    local -r xmlfile="artifacts/subtask-logs/${1}/sponge_log.xml"

    export NAME="${1}"
    export FAILURE=$(cat "${2}")
    envsubst < kokoro/helpers/test_failure.xml.tpl > "$xmlfile"
}

function collect_test_logs {
    mkdir --parents artifacts/bazel-testlogs

    # Copy all test.log and test.xml for the most recent bazel test run into our artifacts directory.
    fd "^test.log$" "bazel-testlogs" --exec cp --parents --force --preserve=timestamps {} artifacts
    fd "^test.xml$" "bazel-testlogs" --exec cp --parents --force --preserve=timestamps {} artifacts

    # Rename the files to the name that will let them be parsed as sponge logs.
    fd "^test.log" artifacts/bazel-testlogs --exec mv {} "{//}/sponge_log.log"
    fd "^test.xml" artifacts/bazel-testlogs --exec mv {} "{//}/sponge_log.xml"
}
