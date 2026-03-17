set working-directory := '..'

import 'copy_helpers.just'

# Recipes for running Oak launchers locally.

[private]
default:
    @just --list run

[private]
oak-functions-containers-launcher-artifacts: \
    (copy-binary "stage0_bin" "stage0_bin") \
    (copy-binary "oak_containers/kernel" "oak_containers_kernel") \
    (copy-binary "oak_containers/stage1_bin:stage1.cpio" "oak_containers_stage1") \
    (copy-binary "oak_containers/system_image/oak_containers_system_image.tar.xz" "oak_containers_system_image") \
    (copy-binary "oak_functions_containers_app/bundle.tar" "oak_functions_containers_bundle") \
    (copy-binary "oak_functions_containers_launcher" "oak_functions_containers_launcher")

[doc("""
Run the Oak Functions containers launcher.

Builds all required artifacts first, then launches with the given Wasm
target. To enable logging, prefix your command with RUST_LOG=debug.
""")]
oak-functions-containers-launcher wasm_target port lookup_data_path communication_channel virtio_guest_cid: oak-functions-containers-launcher-artifacts
    bazel build -c opt {{wasm_target}}
    artifacts/binaries/oak_functions_containers_launcher \
        --vmm-binary=$(which qemu-system-x86_64) \
        --stage0-binary=artifacts/binaries/stage0_bin \
        --kernel=artifacts/binaries/oak_containers_kernel \
        --initrd=artifacts/binaries/oak_containers_stage1 \
        --system-image=artifacts/binaries/oak_containers_system_image \
        --container-bundle=artifacts/binaries/oak_functions_containers_bundle \
        --ramdrive-size=1000000 \
        --memory-size=2G \
        --wasm=$(bazel cquery -c opt {{wasm_target}} --output files) \
        --port={{port}} \
        --lookup-data={{lookup_data_path}} \
        --virtio-guest-cid={{virtio_guest_cid}} \
        --communication-channel={{communication_channel}}

[private]
oak-restricted-kernel-launcher-artifacts: \
    (copy-binary "stage0_bin" "stage0_bin") \
    (copy-binary "enclave_apps/oak_echo_enclave_app" "oak_echo_enclave_app") \
    (copy-binary "enclave_apps/oak_orchestrator" "oak_orchestrator") \
    (copy-binary "oak_restricted_kernel_launcher" "oak_restricted_kernel_launcher") \
    (copy-binary "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin" "") \
    (copy-binary "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_serial_channel_bin" "")

[doc("""
Run the Oak Restricted Kernel launcher with the echo enclave app.

Builds all required artifacts first. Runs with RUST_LOG=DEBUG enabled.
""")]
oak-restricted-kernel-launcher: oak-restricted-kernel-launcher-artifacts
    RUST_LOG=DEBUG artifacts/binaries/oak_restricted_kernel_launcher \
        --bios-binary=artifacts/binaries/stage0_bin \
        --kernel=artifacts/binaries/oak_restricted_kernel_wrapper_virtio_console_channel_bin \
        --vmm-binary=$(which qemu-system-x86_64) \
        --app-binary=artifacts/binaries/oak_echo_enclave_app \
        --initrd=artifacts/binaries/oak_orchestrator \
        --memory-size=256M

[private]
oak-functions-launcher-artifacts: \
    (copy-binary "stage0_bin" "stage0_bin") \
    (copy-binary "enclave_apps/oak_functions_enclave_app" "oak_functions_enclave_app") \
    (copy-binary "enclave_apps/oak_orchestrator" "oak_orchestrator") \
    (copy-binary "oak_functions_launcher" "oak_functions_launcher") \
    (copy-binary "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin" "")

[doc("""
Run the Oak Functions launcher on the restricted kernel.

Builds all required artifacts first, then launches with the given Wasm
target. To enable logging, prefix your command with RUST_LOG=debug.
""")]
oak-functions-launcher wasm_target port lookup_data_path: oak-functions-launcher-artifacts
    bazel build -c opt {{wasm_target}}
    artifacts/binaries/oak_functions_launcher \
        --bios-binary=artifacts/binaries/stage0_bin \
        --kernel=artifacts/binaries/oak_restricted_kernel_wrapper_virtio_console_channel_bin \
        --vmm-binary=$(which qemu-system-x86_64) \
        --app-binary=artifacts/binaries/oak_functions_enclave_app \
        --initrd=artifacts/binaries/oak_orchestrator \
        --memory-size=256M \
        --wasm=$(bazel cquery -c opt {{wasm_target}} --output files) \
        --port={{port}} \
        --lookup-data={{lookup_data_path}}
