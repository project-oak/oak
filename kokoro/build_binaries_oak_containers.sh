#!/usr/bin/env bash

set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

export CI=kokoro
export RUST_BACKTRACE=1
export RUST_LOG=debug
export XDG_RUNTIME_DIR=/var/run

# Make sure we're in the root of the repository.
cd "$(dirname "$0")/.."

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
readonly generated_binaries=(
    ./target/stage1.cpio
    ./oak_containers_kernel/target/bzImage
    ./oak_containers_kernel/cmd_line_regex.txt
    ./oak_containers_system_image/target/image.tar.xz
    ./oak_containers_hello_world_container/target/oak_container_example_oci_filesystem_bundle.tar
    ./oak_functions_containers_container/target/oak_functions_container_oci_filesystem_bundle.tar
    ./oak_functions_containers_container/target/oak_functions_insecure_container_oci_filesystem_bundle.tar

    # We track these binaries so that we can monitor their reproducibility, while b/311651716 is completed.
    # We do not expect to import them in google3, since they are part of the system image, which is
    # not reproducibly buildable yet.
    ./oak_containers_system_image/target/oak_containers_orchestrator
    ./oak_containers_system_image/target/oak_containers_syslogd
)
readonly binary_names=(
    oak_containers_stage1
    oak_containers_kernel
    oak_containers_kernel_cmd_line_regex
    oak_containers_system_image
    oak_containers_hello_world_container
    oak_functions_container
    oak_functions_insecure_container

    oak_containers_orchestrator
    oak_containers_syslogd
)
for i in "${!binary_names[@]}"; do
    cp --preserve=timestamps \
        "${generated_binaries[$i]}" \
        "${KOKORO_ARTIFACTS_DIR}/binaries/${binary_names[$i]}"
done

ls -alsR "${KOKORO_ARTIFACTS_DIR}/binaries"

# Print binary digests (ignore failures, e.g. for directories).
sha256sum "${KOKORO_ARTIFACTS_DIR}"/binaries/* || true
