set working-directory := '..'

import 'copy_helpers.just'

# Recipes used by GitHub Actions to build targets for transparent release.
# Each recipe corresponds to a buildconfig in `buildconfigs/*.sh`.

[private]
default:
    @just --list github

key_xor_test_app: \
    (copy-binary "enclave_apps/key_xor_test_app" "key_xor_test_app")

oak_client_android_app: \
    (copy-binary "java/src/main/java/com/google/oak/client/android:client_app.apk" "client_app.apk")

oak_containers_agent: \
    (copy-binary "oak_containers/agent:bin/oak_containers_agent" "oak_containers_agent")

oak_containers_kernel: \
    (copy-binary "oak_containers/kernel" "oak_containers_kernel") \
    (copy-subjects "oak_containers/kernel:subjects" "oak_containers_kernel")

oak_containers_nvidia_system_image: \
    (copy-binary "oak_containers/system_image/oak_containers_nvidia_system_image.tar.xz" "oak_containers_nvidia_system_image.tar.xz")

oak_containers_orchestrator: \
    (copy-binary "oak_containers/orchestrator_bin:bin/oak_containers_orchestrator" "oak_containers_orchestrator")

stage1_cpio: \
    (copy-binary "oak_containers/stage1_bin:stage1.cpio" "stage1.cpio")

oak_containers_syslogd: \
    (copy-binary "oak_containers/syslogd" "oak_containers_syslogd")

# Included jemalloc to debug possible reproducibility issue.
oak_containers_system_image: \
    (copy-binary "oak_containers/system_image/oak_containers_system_image.tar.xz" "oak_containers_system_image.tar.xz") \
    (copy-all "@jemalloc" "jemalloc")

oak_echo_enclave_app: \
    (copy-binary "enclave_apps/oak_echo_enclave_app" "oak_echo_enclave_app")

oak_echo_raw_enclave_app: \
    (copy-binary "enclave_apps/oak_echo_raw_enclave_app" "oak_echo_raw_enclave_app")

oak_logcabin_endorser_enclave_app: \
    (copy-binary "enclave_apps/oak_logcabin_endorser_enclave_app" "oak_logcabin_endorser_enclave_app")

oak_functions_enclave_app: \
    (copy-binary "enclave_apps/oak_functions_enclave_app" "oak_functions_enclave_app")

oak_functions_insecure_enclave_app: \
    (copy-binary "enclave_apps/oak_functions_enclave_app:oak_functions_insecure_enclave_app" "oak_functions_insecure_enclave_app")

oak_orchestrator: \
    (copy-binary "enclave_apps/oak_orchestrator" "oak_orchestrator")

oak_restricted_kernel_wrapper_simple_io_channel: \
    (copy-binary "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_simple_io_channel_bin" "oak_restricted_kernel_simple_io_init_rd_wrapper_bin") \
    (copy-subjects "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_simple_io_channel_measurement" "")

[working-directory: 'oak_private_memory']
private_memory_enclave_app:
    just private-memory-enclave-bundle-tar

[working-directory: 'oak_private_memory']
private_memory_server:
    just private-memory-server

stage0_bin_tdx: (copy-binary "stage0_bin_tdx" "stage0_bin_tdx")

stage0_bin: \
    (copy-binary "stage0_bin" "stage0_bin") \
    (copy-subjects "stage0_bin:subjects" "stage0_bin")
