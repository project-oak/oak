
# A helper function used by build_test_and_copy_to_placer.sh
function copy_binaries_to_placer() {
    mkdir -p "${KOKORO_ARTIFACTS_DIR}/binaries/"

    # Copy the generated binaries to Placer. The timestamps are used to convey
    # the creation time.
    #
    # System image deps (oak_containers_orchestrator, oak_containers_syslogd,
    # oak_containers_agent) are tracked to monitor their reproducibility. They are
    # expected to be imported transiently into google3 for the sake of provenance
    # verification (i.e., do Kokoro and GitHub produce identical results).
    readonly generated_binaries=(
        artifacts/oak_containers_agent
        artifacts/oak_containers_kernel
        artifacts/oak_containers_nvidia_system_image.tar.xz
        artifacts/oak_containers_orchestrator
        artifacts/oak_containers_syslogd
        artifacts/oak_containers_system_image.tar.xz
        artifacts/oak_functions_containers_app_bundle.tar
        artifacts/oak_functions_containers_app_bundle_insecure.tar
        artifacts/rust_hello_world_enclave_bundle.tar
        artifacts/stage1.cpio
        artifacts/enclave_apps/key_xor_test_app
        artifacts/client_app.apk
        artifacts/enclave_apps/oak_echo_enclave_app
        artifacts/enclave_apps/oak_echo_raw_enclave_app
        artifacts/enclave_apps/oak_functions_enclave_app
        artifacts/enclave_apps/oak_functions_insecure_enclave_app
        artifacts/enclave_apps/oak_orchestrator
        artifacts/oak_restricted_kernel_wrapper_simple_io_channel_bin
        artifacts/stage0_bin
        artifacts/stage0_bin_tdx
        artifacts/private_memory_server
    )
    readonly binary_names=(
        oak_containers_agent
        oak_containers_kernel
        oak_containers_nvidia_system_image
        oak_containers_orchestrator
        oak_containers_syslogd
        oak_containers_system_image
        oak_functions_container
        oak_functions_insecure_container
        oak_containers_hello_world_container
        oak_containers_stage1
        key_xor_test_app
        oak_client_android_app
        oak_echo_enclave_app
        oak_echo_raw_enclave_app
        oak_functions_enclave_app
        oak_functions_insecure_enclave_app
        oak_orchestrator
        oak_restricted_kernel_simple_io_init_rd_wrapper_bin
        stage0_bin
        stage0_bin_tdx
        private_memory_server
    )
    for i in "${!binary_names[@]}"; do
        cp --preserve=timestamps \
            "${generated_binaries[$i]}" \
            "${KOKORO_ARTIFACTS_DIR}/binaries/${binary_names[$i]}"
    done

    ls -alsR "${KOKORO_ARTIFACTS_DIR}/binaries"

    # Print binary digests (ignore failures, e.g. for directories).
    sha256sum "${KOKORO_ARTIFACTS_DIR}"/binaries/* || true

    # Store the git commit hash in the name of an empty file, so that it can
    # be efficiently found via a glob.
    touch "${KOKORO_ARTIFACTS_DIR}/binaries/git_commit_${KOKORO_GIT_COMMIT_oak:?}"
}
