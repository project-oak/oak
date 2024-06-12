# This file is conceptually similar to a Makefile, but uses the `just` tool, which has a more reasonable syntax.
#
# See:
#
# - https://github.com/casey/just
# - https://just.systems/man/en/

export BAZEL_CONFIG_FLAG := if env_var_or_default('CI', '') == "" { "" } else { "--config=ci" }

key_xor_test_app: (build_enclave_app "key_xor_test_app")
oak_echo_enclave_app: (build_enclave_app "oak_echo_enclave_app")
oak_echo_raw_enclave_app: (build_enclave_app "oak_echo_raw_enclave_app")
oak_functions_enclave_app: (build_enclave_app "oak_functions_enclave_app")
oak_orchestrator: (build_enclave_app "oak_orchestrator")

all_enclave_apps: key_xor_test_app oak_echo_enclave_app oak_echo_raw_enclave_app oak_functions_enclave_app oak_functions_insecure_enclave_app oak_orchestrator

# Build a single enclave app, given its name.
build_enclave_app name:
    env --chdir=enclave_apps/{{name}} cargo build --release

oak_functions_insecure_enclave_app:
    env --chdir=enclave_apps/oak_functions_enclave_app cargo build --release --no-default-features --features=allow_sensitive_logging

oak_restricted_kernel_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --bin=oak_restricted_kernel_bin

# Builds a variant of the restricted kernel and creates a bzImage of it.
# Then creates provenance subjects for it.
restricted_kernel_bzimage_and_provenance_subjects kernel_bin_prefix:
    env \
        --chdir=oak_restricted_kernel_wrapper OAK_RESTRICTED_KERNEL_FILE_NAME={{kernel_bin_prefix}}_bin cargo build \
        --release
    mkdir \
        --parents \
        ./oak_restricted_kernel_wrapper/target/released_bin_with_components_{{kernel_bin_prefix}}
    rust-objcopy \
        --output-target=binary \
        oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/oak_restricted_kernel_wrapper \
        oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/{{kernel_bin_prefix}}_wrapper_bin
    just bzimage_provenance_subjects \
        {{kernel_bin_prefix}} \
        oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/{{kernel_bin_prefix}}_wrapper_bin \
        oak_restricted_kernel_wrapper/bin/{{kernel_bin_prefix}}/subjects

# Create provenance subjects for a kernel bzImage, by extracting the setup data
# and image to the output directory.
bzimage_provenance_subjects kernel_name bzimage_path output_dir:
    rm --recursive --force {{output_dir}}
    mkdir --parents {{output_dir}}
    cargo run --package=oak_kernel_measurement -- \
        --kernel={{bzimage_path}} \
        --kernel-setup-data-output="{{output_dir}}/{{kernel_name}}_setup_data" \
        --kernel-image-output="{{output_dir}}/{{kernel_name}}_image"

oak_restricted_kernel_wrapper: oak_restricted_kernel_bin
    just restricted_kernel_bzimage_and_provenance_subjects oak_restricted_kernel

oak_restricted_kernel_simple_io_init_rd_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --no-default-features --features=simple_io_channel --bin=oak_restricted_kernel_simple_io_init_rd_bin

oak_restricted_kernel_simple_io_init_rd_wrapper: oak_restricted_kernel_simple_io_init_rd_bin
    just restricted_kernel_bzimage_and_provenance_subjects oak_restricted_kernel_simple_io_init_rd

oak_client_android_app:
    bazel build --config=unsafe-fast-presubmit --compilation_mode opt \
        //java/src/main/java/com/google/oak/client/android:client_app
    # Copy out to a directory which does not change with bazel config and does
    # not interfere with cargo. It should be reused for other targets as well.
    mkdir --parents generated
    cp --preserve=timestamps --no-preserve=mode \
        bazel-bin/java/src/main/java/com/google/oak/client/android/client_app.apk \
        generated

stage0_bin:
    env --chdir=stage0_bin \
        cargo objcopy --release -- --output-target=binary \
        target/x86_64-unknown-none/release/stage0_bin

stage0_provenance_subjects output_dir="stage0_bin/bin/subjects": stage0_bin
    rm --recursive --force {{output_dir}}
    mkdir --parents {{output_dir}}
    cargo run --package=snp_measurement --quiet -- \
        --vcpu-count=1,2,4,8,16,32,64 \
        --stage0-rom=stage0_bin/target/x86_64-unknown-none/release/stage0_bin \
        --attestation-measurements-output-dir={{output_dir}}

stage1_cpio:
    env --chdir=oak_containers_stage1 make

oak_containers_kernel:
    env --chdir=oak_containers_kernel make
    just bzimage_provenance_subjects \
        oak_containers_kernel \
        oak_containers_kernel/target/bzImage \
        oak_containers_kernel/bin/subjects

oak_containers_launcher:
    env cargo build --release --package='oak_containers_launcher'

oak_containers_system_image: oak_containers_agent oak_containers_orchestrator oak_containers_syslogd
    echo "Using bazel config flag: $BAZEL_CONFIG_FLAG"
    # Copy dependencies into bazel build.
    mkdir --parents oak_containers_system_image/target/image_binaries
    cp --preserve=timestamps \
        oak_containers_orchestrator/target/oak_containers_orchestrator \
        oak_containers_system_image/target/image_binaries/oak_containers_orchestrator
    cp --preserve=timestamps \
        oak_containers_syslogd/target/oak_containers_syslogd_patched \
        oak_containers_system_image/target/image_binaries/oak_containers_syslogd
    cp --preserve=timestamps \
        oak_containers_agent/target/oak_containers_agent_patched \
        oak_containers_system_image/target/image_binaries/oak_containers_agent
    # Build and compress.
    bazel build $BAZEL_CONFIG_FLAG oak_containers_system_image --build_tag_filters=+noci
    cp --preserve=timestamps \
        bazel-bin/oak_containers_system_image/oak_containers_system_image.tar \
        oak_containers_system_image/target/image.tar
    xz --force oak_containers_system_image/target/image.tar

oak_containers_nvidia_system_image: oak_containers_system_image
    bazel build $BAZEL_CONFIG_FLAG oak_containers_system_image:oak_containers_nvidia_system_image --build_tag_filters=+noci
    cp --preserve=timestamps \
        bazel-bin/oak_containers_system_image/oak_containers_nvidia_system_image.tar \
        oak_containers_system_image/target/nvidia_image.tar
    xz --force oak_containers_system_image/target/nvidia_image.tar

oak_containers_orchestrator:
    env --chdir=oak_containers_orchestrator \
        cargo build --profile=release-lto --target=x86_64-unknown-linux-musl \
        -Z unstable-options --out-dir=target

oak_containers_syslogd:
    env --chdir=oak_containers_syslogd \
        cargo build --release -Z unstable-options --out-dir=target
    # We can't patch the binary in-place, as that would confuse cargo.
    # Therefore we copy it to a new location and patch there.
    cp \
        oak_containers_syslogd/target/oak_containers_syslogd \
        oak_containers_syslogd/target/oak_containers_syslogd_patched
    patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 --set-rpath "" \
        oak_containers_syslogd/target/oak_containers_syslogd_patched

oak_containers_agent:
    env --chdir=oak_containers_agent \
        cargo build --release -Z unstable-options --out-dir=target
    # We can't patch the binary in-place, as that would confuse cargo.
    # Therefore we copy it to a new location and patch there.
    cp \
        oak_containers_agent/target/oak_containers_agent \
        oak_containers_agent/target/oak_containers_agent_patched
    patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 --set-rpath "" \
        oak_containers_agent/target/oak_containers_agent_patched

# Profile the Wasm execution and generate a flamegraph.
profile_wasm:
    # If it fails with SIGSEGV, try running again.
    cargo bench --package=oak_functions_service --bench=wasm_benchmark --features=wasmtime flamegraph -- --profile-time=5
    google-chrome ./target/criterion/flamegraph/profile/flamegraph.svg

# Oak Containers Hello World entry point.

oak_containers_hello_world_container_bundle_tar:
    env --chdir=oak_containers_hello_world_container DOCKER_BUILDKIT=0 bash build_container_bundle

cc_oak_containers_hello_world_container_bundle_tar:
    echo "Using bazel config flag: $BAZEL_CONFIG_FLAG"
    env bazel build $BAZEL_CONFIG_FLAG --compilation_mode opt //cc/containers/hello_world_trusted_app:bundle.tar

oak_containers_hello_world_untrusted_app:
    env cargo build --release --package='oak_containers_hello_world_untrusted_app'

all_oak_containers_binaries: stage0_bin stage1_cpio oak_containers_kernel oak_containers_system_image oak_containers_hello_world_container_bundle_tar cc_oak_containers_hello_world_container_bundle_tar oak_containers_hello_world_untrusted_app

# Oak Functions Containers entry point.

oak_functions_containers_container_bundle_tar:
    env --chdir=oak_functions_containers_container DOCKER_BUILDKIT=0 bash build_container_bundle

oak_functions_containers_launcher:
    env cargo build --release --package='oak_functions_containers_launcher'

all_oak_functions_containers_binaries: stage0_bin stage1_cpio oak_containers_kernel oak_containers_system_image oak_functions_containers_container_bundle_tar oak_functions_containers_launcher

ensure_no_std package:
    RUSTFLAGS="-C target-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float" cargo build --target=x86_64-unknown-none --package='{{package}}'

all_ensure_no_std: (ensure_no_std "micro_rpc") (ensure_no_std "oak_attestation_verification") (ensure_no_std "oak_restricted_kernel_sdk")

# Entry points for Kokoro CI.

kokoro_build_binaries_rust: all_enclave_apps oak_restricted_kernel_bin \
    oak_restricted_kernel_simple_io_init_rd_wrapper stage0_bin \
    oak_client_android_app

kokoro_oak_containers: all_oak_containers_binaries oak_functions_containers_container_bundle_tar
    OAK_CONTAINERS_BINARIES_ALREADY_BUILT=1 RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar --package='oak_containers_hello_world_untrusted_app'

kokoro_run_tests: all_ensure_no_std
    RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar --workspace --exclude='oak_containers_hello_world_untrusted_app'

clang-tidy:
    bazel build $BAZEL_CONFIG_FLAG --config=clang-tidy //cc/...

# TODO: b/343228114 - Use a Bazel tag instead of listing packages here.
bare_metal_crates := "//oak_linux_boot_params //oak_channel //oak_core //oak_virtio //third_party/rust-hypervisor-firmware-virtio //micro_rpc //oak_proto_rust //oak_sev_snp_attestation_report //oak_sev_guest //sev_serial //oak_crypto"

bazel-ci:
    bazel build --config=unsafe-fast-presubmit -- //...:all
    bazel test --config=unsafe-fast-presubmit --test_output=errors -- //...:all

    # Some crates also need to be built for x86_64-unknown-none.
    bazel build --config=unsafe-fast-presubmit --platforms=//:x86_64-unknown-none -- {{bare_metal_crates}}

    # Test Oak as a dependency in the test workspace
    # Protos don't work yet, so just testing a subset of targets
    cd bazel/test_workspace && bazel build --config=unsafe-fast-presubmit @oak2//micro_rpc @oak2//oak_grpc_utils

bazel-clippy:
    bazel build --config=clippy --config=unsafe-fast-presubmit //...:all -- -third_party/...

bazel-rustfmt:
    bazel build --config=rustfmt --config=unsafe-fast-presubmit //...:all -- -third_party/...

xtask job:
    ./scripts/xtask {{job}}

clippy-ci: (xtask "run-cargo-clippy") bazel-clippy
check-format-ci: (xtask "check-format") bazel-rustfmt

# Temporary target to help debugging Bazel remote cache with more detailed logs.
# It should be deleted when debugging is completed.
# TODO: b/337266665 - Remove bazel-cache-test logic once we are satisfied with remote cache hits.
bazel-cache-test:
    mkdir --parents target
    bazel test --config=unsafe-fast-presubmit --build_event_text_file=./target/bazel_bep_1.txt --execution_log_binary_file=./target/bazel_exec_1.log -- //cc/bazel_cache_test:test
