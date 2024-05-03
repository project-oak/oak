# This file is conceptually similar to a Makefile, but uses the `just` tool, which has a more reasonable syntax.
#
# See:
#
# - https://github.com/casey/just
# - https://just.systems/man/en/

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
        ./oak_restricted_kernel_wrapper/bin/{{kernel_bin_prefix}}/subjects \
        oak_restricted_kernel_wrapper/target/x86_64-unknown-none/release/{{kernel_bin_prefix}}_wrapper_bin

# Create provenance subjects for a kernel bzImage, by extracting the setup data
# and image from it. Places them alongside the bzImage in the output directory.
bzimage_provenance_subjects kernel_name output_dir_provenance_subjects bzimage_path:
    rm --recursive --force {{output_dir_provenance_subjects}}
    mkdir --parents {{output_dir_provenance_subjects}}
    cargo run --package=oak_kernel_measurement -- \
        --kernel={{bzimage_path}} \
        --kernel-setup-data-output="{{output_dir_provenance_subjects}}/{{kernel_name}}_setup_data" \
        --kernel-image-output="{{output_dir_provenance_subjects}}/{{kernel_name}}_image"
    cp \
        --preserve=timestamps \
        {{bzimage_path}} \
        {{output_dir_provenance_subjects}}/{{kernel_name}}_bzimage

oak_restricted_kernel_wrapper: oak_restricted_kernel_bin
    just restricted_kernel_bzimage_and_provenance_subjects oak_restricted_kernel

oak_restricted_kernel_simple_io_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --no-default-features --features=simple_io_channel --bin=oak_restricted_kernel_simple_io_bin

oak_restricted_kernel_simple_io_wrapper: oak_restricted_kernel_simple_io_bin
    just restricted_kernel_bzimage_and_provenance_subjects oak_restricted_kernel_simple_io

oak_restricted_kernel_simple_io_init_rd_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --no-default-features --features=simple_io_channel,initrd --bin=oak_restricted_kernel_simple_io_init_rd_bin

oak_restricted_kernel_simple_io_init_rd_wrapper: oak_restricted_kernel_simple_io_init_rd_bin
    just restricted_kernel_bzimage_and_provenance_subjects oak_restricted_kernel_simple_io_init_rd

stage0_bin output_bin_path="stage0_bin/target/x86_64-unknown-none/release/stage0_bin":
    env --chdir=stage0_bin cargo objcopy --release -- --output-target=binary ../{{output_bin_path}}

stage0_provenance_subjects vcpu_count="1,2,4,8,16,32,64" provenance_subjects_dir="stage0_bin/bin/subjects":
    rm --recursive --force {{provenance_subjects_dir}}
    mkdir -p {{provenance_subjects_dir}}
    just stage0_bin {{provenance_subjects_dir}}/stage0_bin
    cargo run --package=snp_measurement --quiet -- \
        --vcpu-count={{vcpu_count}} \
        --stage0-rom={{provenance_subjects_dir}}/stage0_bin \
        --attestation-measurements-output-dir={{provenance_subjects_dir}}

stage1_cpio:
    env --chdir=oak_containers_stage1 make

oak_containers_kernel:
    env --chdir=oak_containers_kernel make
    just bzimage_provenance_subjects \
        oak_containers_kernel \
        oak_containers_kernel/bin/subjects \
        oak_containers_kernel/target/bzImage

oak_containers_system_image: oak_containers_orchestrator oak_containers_syslogd
    # Copy dependencies into bazel build.
    mkdir --parents oak_containers_system_image/target/image_binaries
    cp --preserve=timestamps \
        oak_containers_orchestrator/target/oak_containers_orchestrator \
        oak_containers_system_image/target/image_binaries/oak_containers_orchestrator
    cp --preserve=timestamps \
        oak_containers_syslogd/target/oak_containers_syslogd_patched \
        oak_containers_system_image/target/image_binaries/oak_containers_syslogd
    # Build and compress.
    bazel build oak_containers_system_image
    cp --preserve=timestamps \
        bazel-bin/oak_containers_system_image/oak_containers_system_image.tar \
        oak_containers_system_image/target/image.tar
    xz --force oak_containers_system_image/target/image.tar

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

# Profile the Wasm execution and generate a flamegraph.
profile_wasm:
    # If it fails with SIGSEGV, try running again.
    cargo bench --package=oak_functions_service --bench=wasm_benchmark --features=wasmtime flamegraph -- --profile-time=5
    google-chrome ./target/criterion/flamegraph/profile/flamegraph.svg

# Oak Containers Hello World entry point.

oak_containers_hello_world_container_bundle_tar:
    env --chdir=oak_containers_hello_world_container DOCKER_BUILDKIT=0 bash build_container_bundle

cc_oak_containers_hello_world_container_bundle_tar:
    env bazel build -c opt //cc/containers/hello_world_trusted_app:bundle.tar

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

kokoro_build_binaries_rust: all_enclave_apps oak_restricted_kernel_bin oak_restricted_kernel_simple_io_bin oak_restricted_kernel_simple_io_wrapper oak_restricted_kernel_simple_io_init_rd_wrapper stage0_bin

kokoro_oak_containers: all_oak_containers_binaries oak_functions_containers_container_bundle_tar
    RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar --package='oak_containers_hello_world_untrusted_app'

kokoro_run_tests: all_ensure_no_std
    RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar --workspace --exclude='oak_containers_hello_world_untrusted_app'

clang-tidy:
    bazel build --config=clang-tidy //cc/...

bazel-ci:
    # The --noshow_progress and --curses=no prevent a lot of progress bar noise in the CI logs.
    #
    # The --show_result leads to all of the built packages being logged at the
    # end, so we can visually verify that CI tasks are building everythign we want.
    #
    # --build_tag_filters=-noci allow us to skip broken/flaky/specialized test
    # targets during CI builds by adding tags = ["noci"]
    bazel build --show_result=1000000 --noshow_progress --curses=no --build_tag_filters=-noci -- //...:all
    bazel test  --noshow_progress --curses=no --build_tag_filters=-noci -- //...:all
