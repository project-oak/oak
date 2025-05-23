# This file is conceptually similar to a Makefile, but uses the `just` tool, which has a more reasonable syntax.
#
# See:
#
# - https://github.com/casey/just
# - https://just.systems/man/en/

# Import justfile.local, if it exists, so that developers can create their own
# justfile commands that might not be generally useful enough to commit to the
# project.
import? "justfile.local"

# Same, but for a user-wide local Oak justfile (works with Git worktrees).
import? "~/.oak_justfile.local"

# Detect the CI job environment so that we can configure bazel commands accordingly.
CI_JOB_TYPE:=env_var_or_default('CI_JOB_TYPE', 'LOCAL')
BAZEL_CONFIG_FLAG := if CI_JOB_TYPE == "PRESUBMIT" {
    "--config=unsafe-fast-presubmit"
} else if CI_JOB_TYPE == "CONTINUOUS" {
    "--config=ci"
} else {
    ""
}

show-bazel-flag:
    echo "CI Job Type: $CI_JOB_TYPE, Bazel Config Flag: "+{{BAZEL_CONFIG_FLAG}}

# Quick-and-dirty Cargo.toml workspace finder for cargo commands.
# We plan to remove Cargo.toml files soon, and then this can go as well.
export CARGO_WORKSPACE_LIST_CMD := 'grep -l "\[workspace" **/Cargo.toml --exclude="third_party/*"'
export CARGO_LOCKFILES_LIST_CMD := 'find . -name "Cargo*.lock"'

# -- DEVELOPER WORKFLOW TOOLS --

# Convenience bundle of tests and checks prior to sending a change for review.
presubmit: \
    format \
    build-and-test \
    clippy-ci \
    cargo-audit \
    cargo-udeps \
    private_memory_presubmit

presubmit-full: \
    presubmit \
    all_ensure_no_std \
    kokoro_build_binaries_rust \
    kokoro_verify_buildconfigs \
    oak_containers_tests \
    kokoro_oak_containers

format:
    bazel build {{BAZEL_CONFIG_FLAG}} linter && bazel-bin/linter/linter --fix

# -- End Developer Workflow Tools --

# -- BUILD ENCLAVE APPS --

build_all_enclave_apps: build_key_xor_test_app build_oak_echo_enclave_app build_oak_echo_raw_enclave_app build_oak_functions_enclave_app build_oak_orchestrator build_oak_functions_insecure_enclave_app

build_key_xor_test_app: (build_enclave_app "key_xor_test_app")
build_oak_echo_enclave_app: (build_enclave_app "oak_echo_enclave_app")
build_oak_echo_raw_enclave_app: (build_enclave_app "oak_echo_raw_enclave_app")
build_oak_multi_process_test: (build_enclave_app "oak_multi_process_test")
build_oak_functions_enclave_app: (build_enclave_app "oak_functions_enclave_app")
build_oak_orchestrator: (build_enclave_app "oak_orchestrator")

# Build a single enclave app, given its name.
build_enclave_app name:
    bazel build {{BAZEL_CONFIG_FLAG}} //enclave_apps/{{name}}
    mkdir --parents artifacts/enclave_apps/
    cp --force --preserve=timestamps \
        bazel-bin/enclave_apps/{{name}}/{{name}} \
        artifacts/enclave_apps/

build_oak_functions_insecure_enclave_app:
    bazel build {{BAZEL_CONFIG_FLAG}} //enclave_apps/oak_functions_enclave_app:oak_functions_insecure_enclave_app
    mkdir --parents artifacts/enclave_apps/
    cp --force --preserve=timestamps \
        bazel-bin/enclave_apps/oak_functions_enclave_app/oak_functions_insecure_enclave_app \
        artifacts/enclave_apps/

# -- END Build Enclave Apps --

run_oak_functions_containers_launcher wasm_path port lookup_data_path communication_channel virtio_guest_cid:
    artifacts/oak_functions_containers_launcher \
        --vmm-binary=$(which qemu-system-x86_64) \
        --stage0-binary=artifacts/stage0_bin \
        --kernel=bazel-bin/oak_containers/kernel/bzImage \
        --initrd=artifacts/stage1.cpio \
        --system-image=artifacts/oak_containers_system_image.tar.xz \
        --container-bundle=bazel-bin/oak_functions_containers_app/bundle.tar \
        --ramdrive-size=1000000 \
        --memory-size=2G \
        --wasm={{wasm_path}} \
        --port={{port}} \
        --lookup-data={{lookup_data_path}} \
        --virtio-guest-cid={{virtio_guest_cid}} \
        --communication-channel={{communication_channel}}

run_oak_functions_launcher wasm_path port lookup_data_path: (restricted_kernel_bzimage_and_provenance_subjects "_virtio_console_channel")
    artifacts/oak_functions_launcher \
        --bios-binary=artifacts/stage0_bin \
        --kernel=oak_restricted_kernel_wrapper/bin/wrapper_bzimage_virtio_console_channel \
        --vmm-binary=$(which qemu-system-x86_64) \
        --app-binary=artifacts/enclave_apps/oak_functions_enclave_app \
        --initrd=artifacts/enclave_apps/oak_orchestrator \
        --memory-size=256M \
        --wasm={{wasm_path}} \
        --port={{port}} \
        --lookup-data={{lookup_data_path}}

# Run an integration test for Oak Functions making sure all the dependencies are built.
run_oak_functions_test: build_oak_orchestrator oak_functions_launcher build_oak_functions_enclave_app (wasm_release_crate "key_value_lookup") oak_restricted_kernel_wrapper_virtio_console_channel
    cargo test --package=key_value_lookup test_server

# Builds a variant of the restricted kernel and creates a bzImage of it.
# Then creates provenance subjects for it.
# kernel_suffix examples: _virtio_console_channel, _simple_io_channel
restricted_kernel_bzimage_and_provenance_subjects kernel_suffix:
    mkdir --parents oak_restricted_kernel_wrapper/bin

    # Building in "opt" mode is required so that Rust won't try to prevent underflows.
    # This check must be OFF otherwise checks will be too conservative and fail at runtime.
    bazel build {{BAZEL_CONFIG_FLAG}} \
        --compilation_mode opt --platforms=//:x86_64-unknown-none \
        //oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper{{kernel_suffix}}_bin

    # Create provenance subjects for a kernel bzImage, by extracting the setup data
    # and image to the output directory.
    bazel build {{BAZEL_CONFIG_FLAG}} --platforms=//:x86_64-unknown-none \
        //oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper{{kernel_suffix}}_measurement

    cp --force --preserve=timestamps --no-preserve=mode \
        bazel-bin/oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper{{kernel_suffix}}* \
        artifacts

    # Place things where they were built in the cargo world for compatiblity.
    cp --force --preserve=timestamps \
        bazel-bin/oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper{{kernel_suffix}}_bin \
        oak_restricted_kernel_wrapper/bin/wrapper_bzimage{{kernel_suffix}}

# Create provenance subjects for a kernel bzImage, by extracting the setup data
# and image to the output directory.
bzimage_provenance_subjects kernel_name bzimage_path output_dir:
    rm --recursive --force {{output_dir}}
    mkdir --parents {{output_dir}}
    bazel run {{BAZEL_CONFIG_FLAG}} //oak_kernel_measurement -- \
        --kernel={{bzimage_path}} \
        --kernel-setup-data-output="{{output_dir}}/{{kernel_name}}_setup_data" \
        --kernel-image-output="{{output_dir}}/{{kernel_name}}_image"

oak_restricted_kernel_bin_virtio_console_channel:
    # Building in "opt" mode is required so that Rust won't try to prevent underflows.
    # This check must be OFF otherwise checks will be too conservative and fail at runtime.
    bazel build {{BAZEL_CONFIG_FLAG}} \
         --compilation_mode opt --platforms=//:x86_64-unknown-none \
        //oak_restricted_kernel_bin:oak_restricted_kernel_bin_virtio_console_channel

oak_restricted_kernel_wrapper_virtio_console_channel:
    just restricted_kernel_bzimage_and_provenance_subjects _virtio_console_channel

oak_restricted_kernel_bin_simple_io_channel:
    bazel build {{BAZEL_CONFIG_FLAG}} --platforms=//:x86_64-unknown-none \
        //oak_restricted_kernel_bin:oak_restricted_kernel_bin_simple_io_channel

oak_restricted_kernel_wrapper_simple_io_channel:
    just restricted_kernel_bzimage_and_provenance_subjects _simple_io_channel

oak_client_android_app:
    bazel build {{BAZEL_CONFIG_FLAG}} \
        //java/src/main/java/com/google/oak/client/android:client_app
    # Copy out to a directory which does not change with bazel config and does
    # not interfere with cargo. It should be reused for other targets as well.
    cp --force --preserve=timestamps --no-preserve=mode \
        bazel-bin/java/src/main/java/com/google/oak/client/android/client_app.apk \
        artifacts

private_memory_presubmit:
    cd oak_private_memory && nix develop --command just presubmit

oak_private_memory:  private_memory_server private_memory_enclave_bundle

private_memory_server: private_memory_presubmit
    cp --force --preserve=timestamps --no-preserve=mode \
        oak_private_memory/bazel-bin/private_memory_server \
        artifacts

private_memory_enclave_bundle: private_memory_presubmit
    cp --force --preserve=timestamps --no-preserve=mode \
        oak_private_memory/bazel-bin/bundle.tar \
        artifacts/private_memory_enclave_bundle.tar

wasm_crate name:
    cargo build --target=wasm32-unknown-unknown -p {{name}}

wasm_release_crate name:
    cargo build --target=wasm32-unknown-unknown --release -p {{name}}

all_wasm_test_crates: (wasm_release_crate "echo") (wasm_release_crate "key_value_lookup") (wasm_release_crate "invalid_module") (wasm_release_crate "oak_functions_test_module") (wasm_release_crate "oak_functions_sdk_abi_test_get_storage_item") (wasm_release_crate "oak_functions_sdk_abi_test_invoke_testing")

stage0_bin:
    bazel build {{BAZEL_CONFIG_FLAG}} --platforms=//:x86_64-firmware \
        //stage0_bin:stage0_bin
    cp --force --preserve=timestamps --no-preserve=mode \
        bazel-bin/stage0_bin/stage0_bin \
        artifacts/stage0_bin
    mkdir -p artifacts/stage0_bin_subjects
    rm --force artifacts/stage0_bin_subjects/*
    bazel run {{BAZEL_CONFIG_FLAG}} //snp_measurement -- \
        --vcpu-count=1,2,4,8,16,32,64 \
        --stage0-rom=$(realpath artifacts/stage0_bin) \
        --attestation-measurements-output-dir=$(realpath artifacts/stage0_bin_subjects)

stage0_bin_tdx:
    bazel build {{BAZEL_CONFIG_FLAG}} --platforms=//:x86_64-firmware \
        //stage0_bin_tdx:stage0_bin_tdx
    cp --force --preserve=timestamps --no-preserve=mode \
        bazel-bin/stage0_bin_tdx/stage0_bin_tdx \
        artifacts/stage0_bin_tdx

stage1_cpio:
    bazel build {{BAZEL_CONFIG_FLAG}} //oak_containers/stage1_bin
    cp --force --preserve=timestamps --no-preserve=mode \
        bazel-bin/oak_containers/stage1_bin/stage1.cpio \
        artifacts

stage1_tdx_cpio:
    bazel build {{BAZEL_CONFIG_FLAG}} //oak_containers/stage1_bin_tdx
    cp --force --preserve=timestamps --no-preserve=mode \
        bazel-bin/oak_containers/stage1_bin_tdx/stage1_tdx.cpio \
        artifacts

oak_containers_kernel:
    bazel build {{BAZEL_CONFIG_FLAG}} //oak_containers/kernel/...
    cp --force --preserve=timestamps \
        bazel-bin/oak_containers/kernel/bzImage \
        artifacts/oak_containers_kernel
    just bzimage_provenance_subjects \
        oak_containers_kernel \
        $(realpath artifacts/oak_containers_kernel) \
        $(realpath oak_containers)/kernel/bin/subjects

oak_containers_launcher:
    bazel build {{BAZEL_CONFIG_FLAG}} //oak_containers/launcher:oak_containers_launcher
    cp --force --preserve=timestamps \
        bazel-bin/oak_containers/launcher/oak_containers_launcher \
        $(realpath artifacts/oak_containers_launcher)

# Profile the Wasm execution and generate a flamegraph.
profile_wasm:
    # If it fails with SIGSEGV, try running again.
    cargo bench --package=oak_functions_service --bench=wasm_benchmark --features=wasmtime flamegraph -- --profile-time=5
    google-chrome ./target/criterion/flamegraph/profile/flamegraph.svg

bazel_wasm name:
    bazel build {{BAZEL_CONFIG_FLAG}} {{name}} --platforms=":wasm32-unknown-unknown"


# Oak Containers Hello World entry point.

oak_containers_hello_world_container_bundle_tar:
    bazel build {{BAZEL_CONFIG_FLAG}} //oak_containers/examples/hello_world/enclave_app:bundle.tar
    # bazel-bin symlink doesn't exist outside of the docker container, this
    # makes the file available to the kokoro script.
    cp --force --preserve=timestamps \
        bazel-bin/oak_containers/examples/hello_world/enclave_app/bundle.tar \
        artifacts/rust_hello_world_enclave_bundle.tar

cc_oak_containers_hello_world_container_bundle_tar:
    bazel build {{BAZEL_CONFIG_FLAG}} //cc/containers/hello_world_enclave_app:bundle.tar

# Oak Functions Containers entry point.

oak_functions_containers_app_bundle_tar:
    bazel build {{BAZEL_CONFIG_FLAG}} oak_functions_containers_app:bundle oak_functions_containers_app:bundle_insecure
    cp --force --preserve=timestamps \
        bazel-bin/oak_functions_containers_app/bundle.tar \
        artifacts/oak_functions_containers_app_bundle.tar

oak_functions_containers_launcher:
    bazel build {{BAZEL_CONFIG_FLAG}} oak_functions_containers_launcher
    cp --force --preserve=timestamps \
        bazel-bin/oak_functions_containers_launcher/oak_functions_containers_launcher \
        artifacts/oak_functions_containers_launcher

oak_functions_launcher:
    bazel build {{BAZEL_CONFIG_FLAG}} oak_functions_launcher
    cp --force --preserve=timestamps \
        bazel-bin/oak_functions_launcher/oak_functions_launcher \
        artifacts/oak_functions_launcher

all_oak_functions_containers_binaries: stage0_bin stage0_bin_tdx stage1_cpio stage1_tdx_cpio \
    oak_containers_kernel oak_containers_system_image \
    oak_functions_containers_app_bundle_tar oak_functions_containers_launcher \
    oak_functions_launcher

ensure_no_std package:
    RUSTFLAGS="-C target-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float" cargo build --target=x86_64-unknown-none --package='{{package}}'

all_ensure_no_std: (ensure_no_std "micro_rpc") (ensure_no_std "oak_attestation_verification") (ensure_no_std "oak_restricted_kernel_sdk")

oak_attestation_explain_wasm:
    env --chdir=oak_attestation_explain_wasm \
    wasm-pack build \
    --target web  # "web" bundles for native web use \
    --release \
    --no-pack # prevents generating a package.json, we don't need it since we don't use a web bundler

# --- KOKORO CI Entry Points ---

check-format:
    bazel build {{BAZEL_CONFIG_FLAG}} linter && bazel-bin/linter/linter --verbose

kokoro_build_binaries_rust: build_all_enclave_apps oak_restricted_kernel_bin_virtio_console_channel \
    oak_restricted_kernel_wrapper_simple_io_channel stage0_bin stage0_bin_tdx \
    oak_client_android_app oak_private_memory

kokoro_verify_buildconfigs:
    ./scripts/test_buildconfigs buildconfigs/*.sh

# Builds and tests all Oak Container binaries.
oak_containers_tests:
    bazel test {{BAZEL_CONFIG_FLAG}} \
        //oak_containers/... \
        //oak_containers/examples/hello_world/host_app:oak_containers_hello_world_host_app_tests

kokoro_oak_containers: oak_functions_containers_app_bundle_tar oak_containers_tests \
    stage0_bin_tdx stage1_tdx_cpio \
    containers_placer_artifacts

# This is for use with the `oak-containers-test.sh` helper script for testing on the TDX machines.
# Ask dingelish@ or jibbl@ for more info.
oak_containers_tdx_testing: stage0_bin_tdx stage1_tdx_cpio \
    oak_containers_kernel \
    oak_containers_tdx_system_image \
    oak_functions_containers_app_bundle_tar \
    oak_containers_nvidia_system_image \
    oak_containers_hello_world_container_bundle_tar \
    oak_containers_launcher containers_placer_artifacts

# --- End Kokoro CI Entry Points ---

clang-tidy:
    bazel build {{BAZEL_CONFIG_FLAG}} --config=clang-tidy //cc/...

# Query crates that needs to be built for bare metal. Bazel cquery outputs one target in each line,
# with format like "//stage0_dice:stage0_dice (f47c594)" so we take the part before " " (using cut)
# and then use `tr` to bring them into a single line.
# We store the command for the query in this variable, but defer executing it
# until usage to prevent bazel invocation on any just invocation.
# Lazy assignment is not yet supported: https://github.com/casey/just/issues/953
bare_metal_crates_query := "kind(\"rust_.*\", //...) intersect attr(\"target_compatible_with\", \"x86_64-none-setting\", //...)"
wasm_crates_query := "kind(\"rust_.*\", //...) intersect attr(\"target_compatible_with\", \"wasm32-none-setting\", //...)"

# Build and test all targets.
# The kokoro script build_test_and_copy_to_placer expects this recipe to
# generate properly optimized and stripped binaries that it will then copy to
# placer. See kokoro/helpers/copy_binaries.sh for the expected outputs.
build-and-test: std-crates bare-metal-crates wasm-crates kokoro_build_binaries_rust asan test-codelab test-workspace

# The list of ASAN targets is currently constrained right now because:
# * ASAN builds/tests are quite a bit slower
# * In some build targets (cargo_build_scripts for example), LD_LIBRARY_PATH is
#   not correct, and libasan can not be found.
asan:
    bazel build {{BAZEL_CONFIG_FLAG}} --config=asan //cc/oak_session/...


std-crates:
    # When no platform is specified, build for Bazel host platform (x86_64, Linux):
    # bazel test will build all targets as well unless --build_tests_only is specified.
    # We can specify it here to make sure .bazelrc changes don't catch us by surprise.
    bazel test {{BAZEL_CONFIG_FLAG}} //...:all

test-workspace:
    # Test Oak as a dependency in the test workspace
    # Some dependencies aren't properly exposed yet, so just testing a subset of targets
    cd bazel/test_workspace && \
        ./bootstrap && CARGO_BAZEL_REPIN=1 bazel build \
            {{BAZEL_CONFIG_FLAG}} @oak2//micro_rpc @oak2//oak_grpc_utils @oak2//oak_proto_rust

test-codelab:
    cd codelab && bazel build //enclave_app:enclave_app


bare-metal-crates:
    #!/bin/bash
    set -o pipefail
    echo "Building bare metal crates": $(bazel query "{{bare_metal_crates_query}}")
    bazel query "{{bare_metal_crates_query}}" | xargs bazel build {{BAZEL_CONFIG_FLAG}} --platforms=//:x86_64-unknown-none

wasm-crates:
    #!/bin/bash
    set -o pipefail
    echo "Building wasm crates": $(bazel query "{{wasm_crates_query}}")
    bazel query "{{wasm_crates_query}}" | xargs bazel build {{BAZEL_CONFIG_FLAG}} --platforms=//:wasm32-unknown-unknown

list-bare-metal-crates:
    bazel query "{{bare_metal_crates_query}}"

bazel-clippy:
    bazel build --keep_going --config=clippy "$@" //...:all -- -third_party/...

bazel-clippy-ci:
    scripts/clippy_clean

bazel-repin-all: bazel-repin bazel-repin-private-memory bazel-repin-codelab

bazel-repin-private-memory:
    cd oak_private_memory && env CARGO_BAZEL_REPIN=true bazel sync --only=oak_crates_index,oak_no_std_crates_index,oak_no_std_no_avx_crates_index

bazel-repin-codelab:
    cd codelab && env CARGO_BAZEL_REPIN=true bazel sync --only=oak_crates_index,oak_no_std_crates_index,oak_no_std_no_avx_crates_index

bazel-repin:
    env CARGO_BAZEL_REPIN=true bazel sync --only=oak_crates_index,oak_no_std_crates_index,oak_no_std_no_avx_crates_index

# Examples:
# just bazel-update-crate curve25519-dalek
# just bazel-update-crate curve25519-dalek@4.1.3
bazel-update-crate crate:
    env CARGO_BAZEL_REPIN={{crate}} bazel sync --only=oak_crates_index,oak_no_std_crates_index,oak_no_std_no_avx_crates_index

bazel-rustfmt:
    bazel build --config=rustfmt {{BAZEL_CONFIG_FLAG}} //...:all -- -third_party/...

clippy: bazel-clippy

clippy-ci: bazel-clippy-ci

cargo-lockfiles:
    #!/bin/sh
    echo $CARGO_LOCKFILES_LIST_CMD
    for lockfile in $({{CARGO_LOCKFILES_LIST_CMD}})
    do
        echo Lockfile: $lockfile
    done

cargo-audit:
    #!/bin/sh
    for lockfile in $({{CARGO_LOCKFILES_LIST_CMD}})
    do
        echo Cargo auditing: $lockfile
        cargo-audit audit -f $lockfile
    done

cargo-deny:
    #!/bin/sh
    for workspace in $({{CARGO_WORKSPACE_LIST_CMD}})
    do
        env --chdir=$(dirname "$workspace") cargo deny check
    done

cargo-udeps:
    #!/bin/sh
    for workspace in $({{CARGO_WORKSPACE_LIST_CMD}})
    do
        env --chdir=$(dirname "$workspace") cargo udeps --all-targets --backend=depinfo --workspace
    done

git-check-diff:
    ./scripts/git_check_diff

# Temporary target to help debugging Bazel remote cache with more detailed logs.
# It should be deleted when debugging is completed.
# TODO: b/337266665 - Remove bazel-cache-test logic once we are satisfied with remote cache hits.
bazel-cache-test:
    mkdir --parents target
    bazel build \
      --config=unsafe-fast-presubmit \
      --build_event_text_file=target/bazel_bep_1.txt \
      --execution_log_binary_file=target/bazel_exec_1.log \
      -- \
      //oak_dice:all
    bazel test \
      --config=unsafe-fast-presubmit \
      --build_event_text_file=target/bazel_bep_2.txt \
      --execution_log_binary_file=target/bazel_exec_2.log \
      -- \
      //cc/bazel_cache_test:test

build-clients:
    bazel build {{BAZEL_CONFIG_FLAG}} //java/src/main/java/com/google/oak/client/oak_functions_client //cc/client:cli

run-java-functions-client addr:
    bazel-out/k8-fastbuild/bin/java/src/main/java/com/google/oak/client/oak_functions_client/oak_functions_client {{addr}}

run-cc-functions-client addr request:
    bazel-out/k8-fastbuild/bin/cc/client/cli {{addr}} {{request}}

containers_placer_artifacts:
    # We need to copy things out of bazel-bin so that the remaining actions in the kokoro_build_containers script can find them
    # TODO: b/376322165 - Remove the need for this
    cp --force --preserve=timestamps \
        bazel-bin/oak_containers/system_image/oak_containers_system_image.tar.xz \
        artifacts/oak_containers_system_image.tar.xz

    cp --force --preserve=timestamps \
        bazel-bin/oak_containers/system_image/oak_containers_nvidia_system_image.tar.xz \
        artifacts/oak_containers_nvidia_system_image.tar.xz

    cp --force --preserve=timestamps \
        bazel-bin/oak_containers/examples/hello_world/enclave_app/bundle.tar \
        artifacts/rust_hello_world_enclave_bundle.tar

    cp --force --preserve=timestamps \
        bazel-bin/oak_functions_containers_app/bundle.tar \
        artifacts/oak_functions_containers_app_bundle.tar
    cp --force --preserve=timestamps \
        bazel-bin/oak_functions_containers_app/bundle_insecure.tar \
        artifacts/oak_functions_containers_app_bundle_insecure.tar

    cp --force --preserve=timestamps bazel-bin/oak_containers/kernel/bzImage artifacts/oak_containers_kernel
    cp --force --preserve=timestamps bazel-bin/oak_containers/agent/bin/oak_containers_agent artifacts
    cp --force --preserve=timestamps bazel-bin/oak_containers/orchestrator_bin/bin/oak_containers_orchestrator artifacts
    cp --force --preserve=timestamps bazel-bin/oak_containers/syslogd/oak_containers_syslogd artifacts

    cp --force --preserve=timestamps --no-preserve=mode \
        bazel-bin/oak_containers/stage1_bin/stage1.cpio \
        artifacts/stage1.cpio

    cp --force --preserve=timestamps --no-preserve=mode \
        bazel-bin/oak_containers/stage1_bin_tdx/stage1_tdx.cpio \
        artifacts

bazel_build_copy package target:
    bazel build {{BAZEL_CONFIG_FLAG}} "{{package}}:{{target}}"
    cp --force --preserve=timestamps "bazel-bin/{{package}}/{{target}}" artifacts

oak_containers_agent: (bazel_build_copy "oak_containers/agent" "bin/oak_containers_agent")
oak_containers_orchestrator: (bazel_build_copy "oak_containers/orchestrator_bin" "bin/oak_containers_orchestrator")
oak_containers_syslogd: (bazel_build_copy "oak_containers/syslogd" "oak_containers_syslogd")

oak_containers_system_image:
    bazel build {{BAZEL_CONFIG_FLAG}} oak_containers/system_image:oak_containers_system_image
    cp --force --preserve=timestamps \
        bazel-bin/oak_containers/system_image/oak_containers_system_image.tar.xz \
        artifacts

oak_containers_tdx_system_image:
    bazel build {{BAZEL_CONFIG_FLAG}} oak_containers/system_image:oak_containers_tdx_system_image
    cp --force --preserve=timestamps \
        bazel-bin/oak_containers/system_image/oak_containers_tdx_system_image.tar.xz \
        artifacts

oak_containers_nvidia_system_image:
    bazel build {{BAZEL_CONFIG_FLAG}} oak_containers/system_image:oak_containers_nvidia_system_image
    cp --force --preserve=timestamps \
        bazel-bin/oak_containers/system_image/oak_containers_nvidia_system_image.tar.xz \
        artifacts
