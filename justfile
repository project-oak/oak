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
    private_memory_presubmit

presubmit-full: \
    presubmit \
    kokoro_verify_buildconfigs

format:
    bazel build linter && bazel-bin/linter/linter --fix

# -- End Developer Workflow Tools --

run_oak_functions_containers_launcher wasm_path port lookup_data_path communication_channel virtio_guest_cid:
    artifacts/binaries/oak_functions_containers_launcher \
        --vmm-binary=$(which qemu-system-x86_64) \
        --stage0-binary=artifacts/binaries/stage0_bin \
        --kernel=artifacts/oak_containers_kernel \
        --initrd=artifacts/binaries/stage1.cpio \
        --system-image=artifacts/binaries/oak_containers_system_image.tar.xz \
        --container-bundle=bazel-bin/oak_functions_containers_app/bundle.tar \
        --ramdrive-size=1000000 \
        --memory-size=2G \
        --wasm={{wasm_path}} \
        --port={{port}} \
        --lookup-data={{lookup_data_path}} \
        --virtio-guest-cid={{virtio_guest_cid}} \
        --communication-channel={{communication_channel}}

run_oak_functions_launcher wasm_path port lookup_data_path:
    artifacts/binaries/oak_functions_launcher \
        --bios-binary=artifacts/binaries/stage0_bin \
        --kernel=oak_restricted_kernel_wrapper/bin/wrapper_bzimage_virtio_console_channel \
        --vmm-binary=$(which qemu-system-x86_64) \
        --app-binary=artifacts/binaries/oak_functions_enclave_app \
        --initrd=artifacts/binaries/oak_orchestrator \
        --memory-size=256M \
        --wasm={{wasm_path}} \
        --port={{port}} \
        --lookup-data={{lookup_data_path}}

# Create provenance subjects for a kernel bzImage, by extracting the setup data
# and image to the output directory.
bzimage_provenance_subjects kernel_name bzimage_path output_dir:
    rm --recursive --force {{output_dir}}
    mkdir --parents {{output_dir}}
    bazel run //oak_kernel_measurement -- \
        --kernel={{bzimage_path}} \
        --kernel-setup-data-output="{{output_dir}}/{{kernel_name}}_setup_data" \
        --kernel-image-output="{{output_dir}}/{{kernel_name}}_image"

provenance-subjects: \
    stage0_bin_subjects \
    oak_containers_kernel_subjects

stage0_bin_subjects: (copy-binary "stage0_bin" "stage0_bin" "//:x86_64-firmware")
    mkdir -p artifacts/subjects/stage0_bin
    rm --force artifacts/stage0_bin_subjects/*
    bazel run //snp_measurement -- \
        --vcpu-count=1,2,4,8,16,32,64 \
        --stage0-rom=$(realpath artifacts/binaries/stage0_bin) \
        --attestation-measurements-output-dir=$(realpath artifacts/subjects/stage0_bin)

oak_containers_kernel_subjects: (copy-binary "oak_containers/kernel:bzImage" "oak_containers_kernel")
    mkdir -p artifacts/subjects/oak_containers_kernel
    just bzimage_provenance_subjects \
        oak_containers_kernel \
        $(realpath artifacts/binaries/oak_containers_kernel) \
        $(realpath artifacts/subjects/oak_containers_kernel)

# Profile the Wasm execution and generate a flamegraph.
profile_wasm:
    # If it fails with SIGSEGV, try running again.
    cargo bench --package=oak_functions_service --bench=wasm_benchmark --features=wasmtime flamegraph -- --profile-time=5
    google-chrome ./target/criterion/flamegraph/profile/flamegraph.svg

oak_attestation_explain_wasm:
    env --chdir=oak_attestation_explain_wasm \
    wasm-pack build \
    --target web  # "web" bundles for native web use \
    --release \
    --no-pack # prevents generating a package.json, we don't need it since we don't use a web bundler

# --- KOKORO CI Entry Points ---

check-format:
    bazel build linter && bazel-bin/linter/linter

kokoro_verify_buildconfigs:
    ./scripts/test_buildconfigs buildconfigs/*.sh

# --- End Kokoro CI Entry Points ---

clang-tidy:
    bazel build --config=clang-tidy //cc/...

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
build-and-test: \
    std-crates \
    bare-metal-crates \
    wasm-crates \
    provenance-subjects \
    test-codelab

build-and-test-and-copy: build-and-test copy-oak-artifacts private-memory-build-and-copy
# The list of ASAN targets is currently constrained right now because:
# * ASAN builds/tests are quite a bit slower
# * In some build targets (cargo_build_scripts for example), LD_LIBRARY_PATH is
#   not correct, and libasan can not be found.
asan:
    bazel build --config=asan //cc/oak_session/...

kokoro-build_test_and_copy_to_placer: \
    sample-just-log \
    (trap-logs "std-crates") \
    (trap-logs "bare-metal-crates") \
    (trap-logs "wasm-crates") \
    (trap-logs "provenance-subjects") \
    (trap-logs "test-codelab") \
    copy-oak-artifacts \
    private-memory-build-and-copy

sample-just-log:
    mkdir -p artifacts/bazel-testlogs/testing1/
    echo "Can I create a new log artifact?" >> artifacts/bazel-testlogs/testing1/sponge_log.log

copy-logs:
    # Only one thread for cp or you may get race conditions when trying to create.
    fd "test.(log|xml)" -L bazel-testlogs/** --threads=1 --exec cp --force --parents --update {} artifacts
    fd "^test.log" artifacts/bazel-testlogs/** --exec mv "{}" "{//}/sponge_log.log"
    fd "^test.xml" artifacts/bazel-testlogs/** --exec mv "{}" "{//}/sponge_log.xml"

# This can be used by calling scripts to ex
trap-logs recipe:
    #!/bin/bash
    function copy_logs() {
      just copy-logs
    }
    trap copy_logs EXIT
    just {{recipe}}

std-crates:
    # When no platform is specified, build for Bazel host platform (x86_64, Linux):
    # bazel test will build all targets as well unless --build_tests_only is specified.
    # We can specify it here to make sure .bazelrc changes don't catch us by surprise.
    bazel test --keep_going //...:all

test-codelab:
    cd codelab && bazel build //enclave_app:enclave_app


bare-metal-crates:
    #!/bin/bash
    set -o pipefail
    echo "Building bare metal crates": $(bazel query "{{bare_metal_crates_query}}")
    bazel query "{{bare_metal_crates_query}}" | xargs bazel build --platforms=//:x86_64-unknown-none

wasm-crates:
    #!/bin/bash
    set -o pipefail
    echo "Building wasm crates": $(bazel query "{{wasm_crates_query}}")
    bazel query "{{wasm_crates_query}}" | xargs bazel build --platforms=//:wasm32-unknown-unknown

list-bare-metal-crates:
    bazel query "{{bare_metal_crates_query}}"

bazel-clippy:
    bazel build --keep_going --config=clippy "$@" //...:all -- -third_party/...

bazel-clippy-ci:
    scripts/clippy_clean

bazel-repin-all: bazel-repin bazel-repin-private-memory bazel-repin-codelab

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
    bazel build --config=rustfmt //...:all -- -third_party/...

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
    bazel build //java/src/main/java/com/google/oak/client/oak_functions_client //cc/client:cli

# OAK PRIVATE MEMORY

private_memory_presubmit:
    cd oak_private_memory && nix develop --command just presubmit

private-memory-build-and-copy:
    cd oak_private_memory && nix develop --command just build-and-test-and-copy

bazel-repin-private-memory:
    cd oak_private_memory && env CARGO_BAZEL_REPIN=true bazel sync --only=oak_crates_index,oak_no_std_crates_index,oak_no_std_no_avx_crates_index


####################
# ARTIFACT COPYING #
####################
clean-artifacts:
    # Removes all ignored files from the specified path
    git clean -X --force artifacts/**

# These are the core rules for copying the supported artifact types into the output directory.
# We use these to keep track of outputs that we want to track through bazel
# configuration changes, share with CI hosts, or publish transparently.
#
# They ensure that the target is built; this should not add too much time, since already-built
# targets will quickly complete the "build" command.

# This target expects a rule that outputs one binary, and copies it to artifacts/binaries with the given name.
copy-binary target dest platform="":
    bazel build {{target}} --platforms={{platform}}
    mkdir --parents artifacts/binaries
    cp --force --preserve=timestamps --no-preserve=mode \
        $(bazel cquery --platforms={{platform}} {{target}} --output files) \
        artifacts/binaries/{{dest}}

# This file copies all outputs of the given target to the artifacts/subjects subdirectory.
copy-subjects target dest platform="":
    mkdir --parents artifacts/subjects/{{dest}}
    bazel build {{target}} --platforms={{platform}}
    cp --force --preserve=timestamps --no-preserve=mode \
        $(bazel cquery --platforms={{platform}} {{target}} --output files) \
        artifacts/subjects/{{dest}}

# These are all oak artifacts that Kokoro build-and-copy expects.
copy-oak-artifacts: \
    (copy-binary "enclave_apps/key_xor_test_app" "key_xor_test_app") \
    (copy-binary "java/src/main/java/com/google/oak/client/android:client_app.apk" "oak_client_android_app") \
    (copy-binary "oak_containers/agent:bin/oak_containers_agent" "oak_containers_agent") \
    (copy-binary "oak_containers/examples/hello_world/enclave_app:bundle.tar" "oak_containers_hello_world_container") \
    (copy-binary "oak_containers/kernel:bzImage" "oak_containers_kernel") \
    (copy-binary "oak_containers/system_image/oak_containers_nvidia_system_image.tar.xz" "oak_containers_nvidia_system_image") \
    (copy-binary "oak_containers/orchestrator_bin:bin/oak_containers_orchestrator" "oak_containers_orchestrator") \
    (copy-binary "oak_containers/stage1_bin:stage1.cpio" "oak_containers_stage1") \
    (copy-binary "oak_containers/stage1_bin_tdx:stage1_tdx.cpio" "oak_containers_stage1_tdx") \
    (copy-binary "oak_containers/syslogd" "oak_containers_syslogd") \
    (copy-binary "oak_containers/system_image/oak_containers_system_image.tar.xz" "oak_containers_system_image") \
    (copy-binary "enclave_apps/oak_echo_enclave_app" "oak_echo_enclave_app") \
    (copy-binary "enclave_apps/oak_echo_raw_enclave_app" "oak_echo_raw_enclave_app") \
    (copy-binary "oak_functions_containers_app/bundle.tar" "oak_functions_container") \
    (copy-binary "oak_functions_containers_app/bundle_insecure.tar" "oak_functions_insecure_container") \
    (copy-binary "enclave_apps/oak_functions_enclave_app" "oak_functions_enclave_app") \
    (copy-binary "enclave_apps/oak_functions_enclave_app:oak_functions_insecure_enclave_app" "oak_functions_insecure_enclave_app") \
    (copy-binary "enclave_apps/oak_orchestrator" "oak_orchestrator") \
    (copy-binary "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_simple_io_channel_bin" "oak_restricted_kernel_simple_io_init_rd_wrapper_bin") \
    (copy-subjects "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_simple_io_channel_measurement" "") \
    (copy-binary "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin" "") \
    (copy-subjects "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_measurement" "") \
    (copy-binary "stage0_bin" "stage0_bin") \
    (copy-binary "stage0_bin_tdx" "stage0_bin_tdx")


### Github Buildconfig rules
### These correspond to the commands in `buildconfigs/*.sh`
github-key_xor_test_app: \
    (copy-binary "enclave_apps/key_xor_test_app" "key_xor_test_app")

github-oak_client_android_app: \
    (copy-binary "java/src/main/java/com/google/oak/client/android:client_app.apk" "client_app.apk")

github-oak_containers_agent: \
    (copy-binary "oak_containers/agent:bin/oak_containers_agent" "oak_containers_agent")

github-oak_containers_kernel: oak_containers_kernel_subjects

github-oak_containers_nvidia_system_image: \
    (copy-binary "oak_containers/system_image/oak_containers_nvidia_system_image.tar.xz" "oak_containers_nvidia_system_image.tar.xz")

github-oak_containers_orchestrator: \
    (copy-binary "oak_containers/orchestrator_bin:bin/oak_containers_orchestrator" "oak_containers_orchestrator")

github-stage1_tdx_cpio: \
    (copy-binary "oak_containers/stage1_bin_tdx:stage1_tdx.cpio" "stage1_tdx.cpio")

github-stage1_cpio: \
    (copy-binary "oak_containers/stage1_bin:stage1.cpio" "stage1.cpio")

github-oak_containers_syslogd: \
    (copy-binary "oak_containers/syslogd" "oak_containers_syslogd")

github-oak_containers_system_image: \
    (copy-binary "oak_containers/system_image/oak_containers_system_image.tar.xz" "oak_containers_system_image.tar.xz")

github-oak_echo_enclave_app: \
    (copy-binary "enclave_apps/oak_echo_enclave_app" "oak_echo_enclave_app")

github-oak_echo_raw_enclave_app: \
    (copy-binary "enclave_apps/oak_echo_raw_enclave_app" "oak_echo_raw_enclave_app")

github-oak_functions_enclave_app: \
    (copy-binary "enclave_apps/oak_functions_enclave_app" "oak_functions_enclave_app")

github-oak_functions_insecure_enclave_app: \
    (copy-binary "enclave_apps/oak_functions_enclave_app:oak_functions_insecure_enclave_app" "oak_functions_insecure_enclave_app")

github-oak_orchestrator: \
    (copy-binary "enclave_apps/oak_orchestrator" "oak_orchestrator")

github-oak_restricted_kernel_wrapper_simple_io_channel: \
    (copy-binary "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_simple_io_channel_bin" "oak_restricted_kernel_simple_io_init_rd_wrapper_bin") \
    (copy-subjects "oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_simple_io_channel_measurement" "")

github-private_memory_enclave_app:
    cd oak_private_memory && just private-memory-enclave-bundle-tar

github-private_memory_server:
    cd oak_private_memory && just private-memory-server

github-stage0_bin_tdx: (copy-binary "stage0_bin_tdx" "stage0_bin_tdx")

github-stage0_bin: (copy-binary "stage0_bin" "stage0_bin") stage0_bin_subjects
