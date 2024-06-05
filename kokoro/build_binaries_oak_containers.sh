#!/usr/bin/env bash

# shellcheck source=./kokoro/common.sh
source "$(dirname "$0")/common.sh"

./scripts/docker_pull
./scripts/docker_run nix develop .#containers --command just kokoro_oak_containers

mkdir -p "${KOKORO_ARTIFACTS_DIR}/test_logs/"
cp --preserve=timestamps \
    ./target/nextest/default/*.xml \
    "${KOKORO_ARTIFACTS_DIR}/test_logs/" || true

mkdir -p "${KOKORO_ARTIFACTS_DIR}/binaries/"

# Store the git commit hash in the name of an empty file, so that it can
# be efficiently found via a glob.
touch "${KOKORO_ARTIFACTS_DIR}/binaries/git_commit_${KOKORO_GIT_COMMIT_oak:?}"

# Copy the generated binaries to Placer. The timestamps are used to convey
# the creation time.
#
# System image deps (oak_containers_orchestrator, oak_containers_syslogd,
# oak_containers_agent) are tracked to monitor their reproducibility. They are
# expected to be imported transiently into google3 for the sake of provenance
# verification (i.e., do Kokoro and GitHub produce identical results).
readonly generated_binaries=(
    ./target/stage1.cpio
    ./oak_containers_kernel/target/bzImage
    ./oak_containers_orchestrator/target/oak_containers_orchestrator
    ./oak_containers_syslogd/target/oak_containers_syslogd_patched
    ./oak_containers_agent/target/oak_containers_agent_patched
    ./oak_containers_system_image/target/image.tar.xz
    ./oak_containers_hello_world_container/target/oak_container_example_oci_filesystem_bundle.tar
    ./oak_functions_containers_container/target/oak_functions_container_oci_filesystem_bundle.tar
    ./oak_functions_containers_container/target/oak_functions_insecure_container_oci_filesystem_bundle.tar
)
readonly binary_names=(
    oak_containers_stage1
    oak_containers_kernel
    oak_containers_orchestrator
    oak_containers_syslogd
    oak_containers_agent
    oak_containers_system_image
    oak_containers_hello_world_container
    oak_functions_container
    oak_functions_insecure_container
)
for i in "${!binary_names[@]}"; do
    cp --preserve=timestamps \
        "${generated_binaries[$i]}" \
        "${KOKORO_ARTIFACTS_DIR}/binaries/${binary_names[$i]}"
done

ls -alsR "${KOKORO_ARTIFACTS_DIR}/binaries"

# Print binary digests (ignore failures, e.g. for directories).
sha256sum "${KOKORO_ARTIFACTS_DIR}"/binaries/* || true
