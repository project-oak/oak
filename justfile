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

export BAZEL_CONFIG_FLAG := if env_var_or_default('CI', '') == "" { "" } else { "--config=ci" }

# Quick-and-dirty Cargo.toml workspace finder for cargo commands.
# We plan to remove Cargo.toml files soon, and then this can go as well.
export CARGO_WORKSPACE_LIST_CMD := 'grep -l "\[workspace" **/Cargo.toml --exclude="third_party/*"'

key_xor_test_app: (build_enclave_app "key_xor_test_app")
oak_echo_enclave_app: (build_enclave_app "oak_echo_enclave_app")
oak_echo_raw_enclave_app: (build_enclave_app "oak_echo_raw_enclave_app")
oak_multi_process_test: (build_enclave_app "oak_multi_process_test")
oak_functions_enclave_app: (build_enclave_app "oak_functions_enclave_app")
oak_orchestrator: (build_enclave_app "oak_orchestrator")

all_enclave_apps: key_xor_test_app oak_echo_enclave_app oak_echo_raw_enclave_app oak_functions_enclave_app oak_functions_insecure_enclave_app oak_orchestrator

# Build a single enclave app, given its name.
build_enclave_app name:
    env --chdir=enclave_apps/{{name}} cargo build --release

oak_functions_insecure_enclave_app:
    env --chdir=enclave_apps/oak_functions_enclave_app cargo build --release --no-default-features --features=allow_sensitive_logging

run_oak_functions_containers_launcher wasm_path port lookup_data_path communication_channel virtio_guest_cid:
    target/x86_64-unknown-linux-gnu/release/oak_functions_containers_launcher \
        --vmm-binary=$(which qemu-system-x86_64) \
        --stage0-binary=generated/stage0_bin \
        --kernel=oak_containers/kernel/target/bzImage \
        --initrd=target/stage1.cpio \
        --system-image=oak_containers/system_image/target/image.tar.xz \
        --container-bundle=oak_functions_containers_container/target/oak_functions_container_oci_filesystem_bundle.tar \
        --ramdrive-size=1000000 \
        --memory-size=2G \
        --wasm={{wasm_path}} \
        --port={{port}} \
        --lookup-data={{lookup_data_path}} \
        --virtio-guest-cid={{virtio_guest_cid}} \
        --communication-channel={{communication_channel}}

run_oak_functions_launcher wasm_path port lookup_data_path:
    target/x86_64-unknown-linux-gnu/release/oak_functions_launcher \
        --bios-binary=generated/stage0_bin \
        --kernel=oak_restricted_kernel_wrapper/bin/wrapper_bzimage_virtio_console_channel \
        --vmm-binary=$(which qemu-system-x86_64) \
        --app-binary=enclave_apps/target/x86_64-unknown-none/release/oak_functions_enclave_app \
        --initrd=enclave_apps/target/x86_64-unknown-none/release/oak_orchestrator \
        --memory-size=256M \
        --wasm={{wasm_path}} \
        --port={{port}} \
        --lookup-data={{lookup_data_path}}

# Run an integration test for Oak Functions making sure all the dependencies are built.
run_oak_functions_test: oak_orchestrator oak_functions_launcher oak_functions_enclave_app (wasm_release_crate "key_value_lookup") oak_restricted_kernel_wrapper_virtio_console_channel
    cargo test --package=key_value_lookup test_server

# Builds a variant of the restricted kernel and creates a bzImage of it.
# Then creates provenance subjects for it.
# kernel_suffix examples: _virtio_console_channel, _simple_io_channel
restricted_kernel_bzimage_and_provenance_subjects kernel_suffix:
    mkdir --parents oak_restricted_kernel_wrapper/bin

    # Buidling in "opt" mode is required so that Rust won't try to prevent underflows.
    # This check must be OFF otherwise checks will be too conservative and fail at runtime.
    bazel build //oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper{{kernel_suffix}}_bin \
        --platforms=//:x86_64-unknown-none \
        --compilation_mode opt

    # Create provenance subjects for a kernel bzImage, by extracting the setup data
    # and image to the output directory.
    bazel build //oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper{{kernel_suffix}}_measurement \
        --platforms=//:x86_64-unknown-none \
        --compilation_mode opt

    mkdir --parents generated
    cp --preserve=timestamps --no-preserve=mode \
        bazel-bin/oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper{{kernel_suffix}}* \
        generated

    # Place things where they were built in the cargo world for compatiblity.
    cp bazel-bin/oak_restricted_kernel_wrapper/oak_restricted_kernel_wrapper{{kernel_suffix}}_bin \
        oak_restricted_kernel_wrapper/bin/wrapper_bzimage{{kernel_suffix}}

# Create provenance subjects for a kernel bzImage, by extracting the setup data
# and image to the output directory.
bzimage_provenance_subjects kernel_name bzimage_path output_dir:
    rm --recursive --force {{output_dir}}
    mkdir --parents {{output_dir}}
    cargo run --package=oak_kernel_measurement -- \
        --kernel={{bzimage_path}} \
        --kernel-setup-data-output="{{output_dir}}/{{kernel_name}}_setup_data" \
        --kernel-image-output="{{output_dir}}/{{kernel_name}}_image"

oak_restricted_kernel_bin_virtio_console_channel:
    # Buidling in "opt" mode is required so that Rust won't try to prevent underflows.
    # This check must be OFF otherwise checks will be too conservative and fail at runtime.
    bazel build //oak_restricted_kernel_bin:oak_restricted_kernel_bin_virtio_console_channel \
        --platforms=//:x86_64-unknown-none \
        --compilation_mode opt

oak_restricted_kernel_wrapper_virtio_console_channel:
    just restricted_kernel_bzimage_and_provenance_subjects _virtio_console_channel

oak_restricted_kernel_bin_simple_io_channel:
    bazel build //oak_restricted_kernel_bin:oak_restricted_kernel_bin_simple_io_channel \
        --platforms=//:x86_64-unknown-none \
        --compilation_mode=opt

oak_restricted_kernel_wrapper_simple_io_channel:
    just restricted_kernel_bzimage_and_provenance_subjects _simple_io_channel

oak_client_android_app:
    bazel build --noexperimental_check_desugar_deps --compilation_mode opt \
        //java/src/main/java/com/google/oak/client/android:client_app
    # Copy out to a directory which does not change with bazel config and does
    # not interfere with cargo. It should be reused for other targets as well.
    mkdir --parents generated
    cp --preserve=timestamps --no-preserve=mode \
        bazel-bin/java/src/main/java/com/google/oak/client/android/client_app.apk \
        generated

wasm_crate name:
    cargo build --target=wasm32-unknown-unknown -p {{name}}

wasm_release_crate name:
    cargo build --target=wasm32-unknown-unknown --release -p {{name}}

all_wasm_test_crates: (wasm_release_crate "echo") (wasm_release_crate "key_value_lookup") (wasm_release_crate "invalid_module") (wasm_release_crate "oak_functions_test_module") (wasm_release_crate "oak_functions_sdk_abi_test_get_storage_item") (wasm_release_crate "oak_functions_sdk_abi_test_invoke_testing")

stage0_bin:
    bazel build //stage0_bin:stage0_bin \
        --platforms=//:x86_64-firmware \
        --compilation_mode opt

    mkdir --parents generated
    cp --preserve=timestamps --no-preserve=mode \
        bazel-bin/stage0_bin/stage0_bin \
        generated

stage0_bin_tdx:
    bazel build //stage0_bin_tdx:stage0_bin_tdx \
        --platforms=//:x86_64-firmware \
        --compilation_mode opt

    mkdir --parents generated
    cp --preserve=timestamps --no-preserve=mode \
        bazel-bin/stage0_bin_tdx/stage0_bin_tdx \
        generated

stage0_provenance_subjects output_dir="stage0_bin/bin/subjects": stage0_bin
    rm --recursive --force {{output_dir}}
    mkdir --parents {{output_dir}}
    cargo run --package=snp_measurement --quiet -- \
        --vcpu-count=1,2,4,8,16,32,64 \
        --stage0-rom=generated/stage0_bin \
        --attestation-measurements-output-dir={{output_dir}}

stage1_cpio:
    env --chdir=oak_containers/stage1 make

oak_containers_kernel:
    env --chdir=oak_containers/kernel make
    just bzimage_provenance_subjects \
        oak_containers_kernel \
        oak_containers/kernel/target/bzImage \
        oak_containers/kernel/bin/subjects

oak_containers_launcher:
    env cargo build --release --package='oak_containers_launcher'

oak_containers_system_image: oak_containers_agent oak_containers_orchestrator oak_containers_syslogd
    echo "Using bazel config flag: $BAZEL_CONFIG_FLAG"
    # Copy dependencies into bazel build.
    mkdir --parents oak_containers/system_image/target/image_binaries
    cp --preserve=timestamps \
        oak_containers/orchestrator/target/oak_containers_orchestrator \
        oak_containers/system_image/target/image_binaries/oak_containers_orchestrator
    cp --preserve=timestamps \
        oak_containers/syslogd/target/oak_containers_syslogd_patched \
        oak_containers/system_image/target/image_binaries/oak_containers_syslogd
    cp --preserve=timestamps \
        oak_containers/agent/target/oak_containers_agent_patched \
        oak_containers/system_image/target/image_binaries/oak_containers_agent
    # Build and compress.
    bazel build $BAZEL_CONFIG_FLAG oak_containers/system_image:oak_containers_system_image --build_tag_filters=+noci
    cp --preserve=timestamps \
        bazel-bin/oak_containers/system_image/oak_containers_system_image.tar \
        oak_containers/system_image/target/image.tar
    xz --force oak_containers/system_image/target/image.tar

oak_containers_nvidia_system_image: oak_containers_system_image
    bazel build $BAZEL_CONFIG_FLAG oak_containers/system_image:oak_containers_nvidia_system_image --build_tag_filters=+noci
    cp --preserve=timestamps \
        bazel-bin/oak_containers/system_image/oak_containers_nvidia_system_image.tar \
        oak_containers/system_image/target/nvidia_image.tar
    xz --force oak_containers/system_image/target/nvidia_image.tar

oak_containers_orchestrator:
    env --chdir=oak_containers/orchestrator \
        cargo build --profile=release-lto --target=x86_64-unknown-linux-musl \
        -Z unstable-options --out-dir=target

oak_containers_syslogd:
    env --chdir=oak_containers/syslogd \
        cargo build --release -Z unstable-options --out-dir=target
    # We can't patch the binary in-place, as that would confuse cargo.
    # Therefore we copy it to a new location and patch there.
    cp \
        oak_containers/syslogd/target/oak_containers_syslogd \
        oak_containers/syslogd/target/oak_containers_syslogd_patched
    patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 --set-rpath "" \
        oak_containers/syslogd/target/oak_containers_syslogd_patched

oak_containers_agent:
    env --chdir=oak_containers/agent \
        cargo build --release -Z unstable-options --out-dir=target
    # We can't patch the binary in-place, as that would confuse cargo.
    # Therefore we copy it to a new location and patch there.
    cp \
        oak_containers/agent/target/oak_containers_agent \
        oak_containers/agent/target/oak_containers_agent_patched
    patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 --set-rpath "" \
        oak_containers/agent/target/oak_containers_agent_patched

# Profile the Wasm execution and generate a flamegraph.
profile_wasm:
    # If it fails with SIGSEGV, try running again.
    cargo bench --package=oak_functions_service --bench=wasm_benchmark --features=wasmtime flamegraph -- --profile-time=5
    google-chrome ./target/criterion/flamegraph/profile/flamegraph.svg

bazel_wasm name:
    bazel build {{name}} --platforms=":wasm32-unknown-unknown"


# Oak Containers Hello World entry point.

oak_containers_hello_world_container_bundle_tar:
    echo "Using bazel config flag: $BAZEL_CONFIG_FLAG"
    env bazel build $BAZEL_CONFIG_FLAG --compilation_mode opt //oak_containers/examples/hello_world/trusted_app:bundle.tar
    # bazel-bin symlink doesn't exist outside of the docker container, this makes the file available to the kokoro script.
    cp bazel-bin/oak_containers/examples/hello_world/trusted_app/bundle.tar target/rust_hello_world_trusted_bundle.tar

cc_oak_containers_hello_world_container_bundle_tar:
    echo "Using bazel config flag: $BAZEL_CONFIG_FLAG"
    env bazel build $BAZEL_CONFIG_FLAG --compilation_mode opt //cc/containers/hello_world_trusted_app:bundle.tar

oak_containers_hello_world_untrusted_app:
    env cargo build --release --package='oak_containers_hello_world_untrusted_app'

all_oak_containers_binaries: stage0_bin stage1_cpio oak_containers_kernel oak_containers_system_image oak_containers_nvidia_system_image oak_containers_hello_world_container_bundle_tar cc_oak_containers_hello_world_container_bundle_tar oak_containers_hello_world_untrusted_app

# Oak Functions Containers entry point.

oak_functions_containers_container_bundle_tar:
    env --chdir=oak_functions_containers_container DOCKER_BUILDKIT=0 bash build_container_bundle

oak_functions_containers_launcher:
    env cargo build --release --package='oak_functions_containers_launcher'

oak_functions_launcher:
    env cargo build --release --package='oak_functions_launcher'

all_oak_functions_containers_binaries: stage0_bin stage1_cpio oak_containers_kernel oak_containers_system_image oak_functions_containers_container_bundle_tar oak_functions_containers_launcher oak_functions_launcher

ensure_no_std package:
    RUSTFLAGS="-C target-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float" cargo build --target=x86_64-unknown-none --package='{{package}}'

all_ensure_no_std: (ensure_no_std "micro_rpc") (ensure_no_std "oak_attestation_verification") (ensure_no_std "oak_restricted_kernel_sdk")

oak_attestation_explain_wasm:
    env --chdir=oak_attestation_explain_wasm \
    wasm-pack build \
    --target web  # "web" bundles for native web use \
    --release \
    --no-pack # prevents generating a package.json, we don't need it since we don't use a web bundler

# Entry points for Kokoro CI.

kokoro_build_binaries_rust: all_enclave_apps oak_restricted_kernel_bin_virtio_console_channel \
    oak_restricted_kernel_wrapper_simple_io_channel stage0_bin \
    oak_client_android_app

kokoro_oak_containers: all_oak_containers_binaries oak_functions_containers_container_bundle_tar
    OAK_CONTAINERS_BINARIES_ALREADY_BUILT=1 RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar --package='oak_containers_hello_world_untrusted_app'

# This list should contain all crates that either a) have tests and are not bazelified yet or b) have bench tests (not supported on Bazel yet).
# TODO: b/349587489 - Bazelify oak_functions_containers_launcher
# TODO: b/353487223 - Add oak_functions_launcher integration tests (also has bench tests).
# TODO: b/349572480 - Enable benchmarks in Bazel and remove oak_functions_service and oak_functions_launcher (after integration tests bazelified) from this list.
cargo_test_packages_arg := "-p key_value_lookup -p oak_functions_containers_launcher -p oak_functions_launcher -p oak_functions_service -p oak_echo_service -p oak_session_wasm"

kokoro_run_cargo_tests: all_ensure_no_std all_oak_functions_containers_binaries oak_restricted_kernel_wrapper_virtio_console_channel oak_orchestrator stage0_bin oak_functions_enclave_app all_wasm_test_crates build-clients
    RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar {{cargo_test_packages_arg}}

clang-tidy:
    bazel build $BAZEL_CONFIG_FLAG --config=clang-tidy //cc/...

# Query crates that needs to be built for bare metal. Bazel cquery outputs one target in each line,
# with format like "//stage0_dice:stage0_dice (f47c594)" so we take the part before " " (using cut)
# and then use `tr` to bring them into a single line.
# We store the command for the query in this variable, but defer executing it
# until usage to prevent bazel invocation on any just invocation.
# Lazy assignment is not yet supported: https://github.com/casey/just/issues/953
bare_metal_crates_query := "bazel cquery 'kind(\"rust_.*\", //...) intersect attr(\"target_compatible_with\", \"x86_64-none-setting\", //...)' --platforms=//:x86_64-unknown-none | cut -d' ' -f1 | tr '\\n' ' '"
wasm_crates_query := "bazel cquery 'kind(\"rust_.*\", //...) intersect attr(\"target_compatible_with\", \"wasm32-none-setting\", //...)' | cut -d' ' -f1 | tr '\\n' ' '"

bazel-ci:
    # Test Oak as a dependency in the test workspace
    # Some dependencies aren't properly exposed yet, so just testing a subset of targets
    cd bazel/test_workspace && CARGO_BAZEL_REPIN=1 bazel build --config=unsafe-fast-presubmit @oak2//micro_rpc @oak2//oak_grpc_utils @oak2//oak_proto_rust

    # When no platform is specified, build for Bazel host platform (x86_64, Linux):
    bazel build --config=unsafe-fast-presubmit -- //...:all
    bazel test --config=unsafe-fast-presubmit --test_output=errors -- //...:all

    # Some crates also need to be built for x86_64-unknown-none and for wasm32-unknown-unknown.
    bazel build --config=unsafe-fast-presubmit --platforms=//:x86_64-unknown-none -- $({{bare_metal_crates_query}})
    bazel build --config=unsafe-fast-presubmit --platforms=//:wasm32-unknown-unknown -- $({{wasm_crates_query}})

list-bare-metal-crates:
    {{bare_metal_crates_query}}

bazel-clippy:
    scripts/clippy_clean

bazel-repin:
    env CARGO_BAZEL_REPIN=true bazel sync --only=oak_crates_index,oak_no_std_crates_index,oak_no_std_no_avx_crates_index

bazel-fmt:
    buildifier -r ${PWD}  # Lints Bazel files - BUILD, WORKSPACE, *.bzl, etc.

bazel-rustfmt:
    bazel build --config=rustfmt --config=unsafe-fast-presubmit //...:all -- -third_party/...

clippy-ci: bazel-clippy cargo-clippy

cargo-clippy:
    #!/bin/sh
    for workspace in $({{CARGO_WORKSPACE_LIST_CMD}})
    do
        env --chdir=$(dirname "$workspace") cargo clippy --all-features --all-targets --no-deps -- --deny=warnings
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


check-format-ci:
    bazel build --config=unsafe-fast-presubmit linter && bazel-bin/linter/linter --verbose

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

format:
    bazel build linter && bazel-bin/linter/linter --fix

build-clients:
    bazel build --config=unsafe-fast-presubmit //java/src/main/java/com/google/oak/client/oak_functions_client //cc/client:cli

run-java-functions-client addr:
    bazel-out/k8-fastbuild/bin/java/src/main/java/com/google/oak/client/oak_functions_client/oak_functions_client {{addr}}

run-cc-functions-client addr request:
    bazel-out/k8-fastbuild/bin/cc/client/cli {{addr}} {{request}}
