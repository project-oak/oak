#!/usr/bin/env bash
#
# Oak's Kokoro presubmit script. Requires bash V4 or later.
#
set -o errexit
set -o nounset
set -o xtrace
set -o pipefail

export CI=kokoro

export RUST_BACKTRACE=1
export RUST_LOG=debug
export XDG_RUNTIME_DIR=/var/run

./scripts/docker_pull
./scripts/docker_run nix develop .#ci --command just kokoro

mkdir -p "$KOKORO_ARTIFACTS_DIR/test_logs/"
cp ./target/nextest/default/*.xml "$KOKORO_ARTIFACTS_DIR/test_logs/"

readonly BINARY_FILE_NAME=binary
readonly binaries_dir="${KOKORO_ARTIFACTS_DIR}/binaries"
readonly commit_hash_dir="${KOKORO_ARTIFACTS_DIR}/git_commit"
mkdir -p "${binaries_dir}" "${commit_hash_dir}"

# Maps binary name to path of build artifact.
declare -A binaries=(
  [oak_restricted_kernel_bin]=./oak_restricted_kernel_bin/target/x86_64-unknown-none/release/oak_restricted_kernel_bin
  [oak_echo_enclave_app]=./enclave_apps/target/x86_64-unknown-none/release/oak_echo_enclave_app
  [oak_echo_raw_enclave_app]=./enclave_apps/target/x86_64-unknown-none/release/oak_echo_raw_enclave_app
  [oak_functions_enclave_app]=./enclave_apps/target/x86_64-unknown-none/release/oak_functions_enclave_app
  [oak_tensorflow_enclave_app]=./enclave_apps/target/x86_64-unknown-none/release/oak_tensorflow_enclave_app
  [quirk_echo_enclave_app]=./enclave_apps/target/x86_64-unknown-none/release/quirk_echo_enclave_app
  [stage0_bin]=./stage0_bin/target/x86_64-unknown-none/release/stage0_bin
)

# Write the commit hash under the commit hash directory, with no contents,
# so no need to open the file, just listing it is sufficient. This is only
# for better performance.
readonly commit_hash="${KOKORO_GIT_COMMIT_oak:?}"
touch "${commit_hash_dir}/${commit_hash}"

# Generate the importer output structure on Placer.
for name in "${!binaries[@]}"; do
  mkdir -p "${binaries_dir}/${name}"
  cp "${binaries[${name}]}" "${binaries_dir}/${name}/${BINARY_FILE_NAME}"

  binary_hash=$(sha256sum --binary "${binaries[${name}]}" | cut -d " " -f 1)
  seconds_since_epoch_utc=$(stat -c "%W" "${binaries[${name}]}")
  cat > "${binaries_dir}/${name}/binary_metadata.textproto" << __EOF__
# proto-file: knowledge/cerebra/oak/release/binary_metadata.proto
# proto-message: oak.BinaryMetadata
name: "${name}"
digests {
  data {
    key: 18
    value: "${binary_hash}"
  }
}
binary_path: "${BINARY_FILE_NAME}"
commit_hash_sha1: "${commit_hash}"
created { seconds: ${seconds_since_epoch_utc} }
__EOF__
done

ls -alsR "${binaries_dir}"
