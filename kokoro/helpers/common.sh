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

function copy_artifacts_to_placer() {
    # Copy the supported artifacts directories to placer.
    cp --recursive --preserve=timestamps \
        artifacts/binaries "${KOKORO_ARTIFACTS_DIR}"
    cp --recursive --preserve=timestamps \
        artifacts/bazel-testlogs "${KOKORO_ARTIFACTS_DIR}"
    cp --recursive --preserve=timestamps \
        artifacts/misc "${KOKORO_ARTIFACTS_DIR}"
    cp --recursive --preserve=timestamps \
        artifacts/subjects "${KOKORO_ARTIFACTS_DIR}"

    # Copy the generated binaries to Placer. The timestamps are used to convey
    # the creation time.
    #
    # System image deps (oak_containers_orchestrator, oak_containers_syslogd,
    # oak_containers_agent) are tracked to monitor their reproducibility. They are
    # expected to be imported transiently into google3 for the sake of provenance
    # verification (i.e., do Kokoro and GitHub produce identical results).
    ls -alsR "${KOKORO_ARTIFACTS_DIR}/binaries"

    # Print binary digests (ignore failures, e.g. for directories).
    sha256sum "${KOKORO_ARTIFACTS_DIR}"/binaries/* || true

    # Store the git commit hash in the name of an empty file, so that it can
    # be efficiently found via a glob.
    touch "${KOKORO_ARTIFACTS_DIR}/binaries/git_commit_${KOKORO_GIT_COMMIT_oak:?}"
}
