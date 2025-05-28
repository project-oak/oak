
# A helper function used by build_test_and_copy_to_placer.sh
function copy_binaries_to_placer() {
    mkdir --parents "${KOKORO_ARTIFACTS_DIR}/binaries/"

    # Copy the generated binaries to Placer. The timestamps are used to convey
    # the creation time.
    #
    # System image deps (oak_containers_orchestrator, oak_containers_syslogd,
    # oak_containers_agent) are tracked to monitor their reproducibility. They are
    # expected to be imported transiently into google3 for the sake of provenance
    # verification (i.e., do Kokoro and GitHub produce identical results).
    cp --recursive --preserve=timestamps \
        artifacts/binaries/* \
        "${KOKORO_ARTIFACTS_DIR}/binaries"

    ls -alsR "${KOKORO_ARTIFACTS_DIR}/binaries"

    # Print binary digests (ignore failures, e.g. for directories).
    sha256sum "${KOKORO_ARTIFACTS_DIR}"/binaries/* || true

    # Store the git commit hash in the name of an empty file, so that it can
    # be efficiently found via a glob.
    touch "${KOKORO_ARTIFACTS_DIR}/binaries/git_commit_${KOKORO_GIT_COMMIT_oak:?}"
}
