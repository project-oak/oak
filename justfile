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

all_enclave_apps: key_xor_test_app oak_echo_enclave_app oak_echo_raw_enclave_app oak_functions_enclave_app oak_functions_insecure_enclave_app

# Build a single enclave app, given its name.
build_enclave_app name:
    env --chdir=enclave_apps/{{name}} cargo build --release

oak_functions_insecure_enclave_app:
    env --chdir=enclave_apps/oak_functions_enclave_app cargo build --release --no-default-features --features=allow_sensitive_logging

oak_restricted_kernel_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --bin=oak_restricted_kernel_bin

oak_restricted_kernel_simple_io_bin:
    env --chdir=oak_restricted_kernel_bin cargo build --release --no-default-features --features=simple_io_channel --bin=oak_restricted_kernel_simple_io_bin

oak_restricted_kernel_wrapper: oak_restricted_kernel_bin
    env --chdir=oak_restricted_kernel_wrapper cargo objcopy --release -- --output-target=binary target/x86_64-unknown-none/release/oak_restricted_kernel_wrapper_bin

stage0_bin:
    env --chdir=stage0_bin cargo objcopy --release -- --output-target=binary target/x86_64-unknown-none/release/stage0_bin

stage1_cpio:
    env --chdir=oak_containers_stage1 make

oak_containers_kernel:
    env --chdir=oak_containers_kernel make

oak_containers_orchestrator:
    cargo build --package=oak_containers_orchestrator --release --target=x86_64-unknown-linux-musl
    mkdir --parents {{oak_containers_system_image_dir}}/target
    cp --force ./target/x86_64-unknown-linux-musl/release/oak_containers_orchestrator {{oak_containers_orchestrator}}

# When built under nix the interpreter points to some nix-specific location that doesn't exist on a regular Linux host, therefore
# we need to manually patch the binary to set it back to the normal regular location.
# But we can't do it in-place, as that would confuse cargo. Therefore we copy the binary to a new location and patch that.
oak_containers_syslogd:
    cargo build --package=oak_containers_syslogd --release
    mkdir --parents {{oak_containers_system_image_dir}}/target
    cp --force ./target/x86_64-unknown-linux-gnu/release/oak_containers_syslogd {{oak_containers_syslogd}}
    patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 {{oak_containers_syslogd}}

oak_containers_system_image_dir := 'oak_containers_system_image'
oak_containers_syslogd := oak_containers_system_image_dir / 'target/oak_containers_syslogd'
oak_containers_orchestrator := oak_containers_system_image_dir / 'target/oak_containers_orchestrator'
oak_containers_system_image_tar := oak_containers_system_image_dir / 'target/image.tar'
oak_containers_system_image_tag := 'oak-containers-system-image:latest'

oak_containers_system_image: oak_containers_orchestrator oak_containers_syslogd
    chmod --recursive a+rX {{oak_containers_system_image_dir}}/files/
    # We need to actually create a container, otherwise we won't be able to use `docker export` that gives us a filesystem image.
    # (`docker save` creates a tarball which has all the layers separate, which is _not_ what we want.)
    docker build ./oak_containers_system_image --tag={{oak_containers_system_image_tag}}
    readonly NEW_DOCKER_CONTAINER_ID="$(docker create {{oak_containers_system_image_tag}})" && \
        docker export "$NEW_DOCKER_CONTAINER_ID" > {{oak_containers_system_image_tar}} && \
        docker rm "$NEW_DOCKER_CONTAINER_ID"
    ls -lah {{oak_containers_system_image_tar}}
    # Hack, as Docker doesn't give us a `/etc/hosts` which means `localhost` won't resolve.
    tar --append --file={{oak_containers_system_image_tar}} --directory={{oak_containers_system_image_dir}}/files etc/hosts
    xz --force {{oak_containers_system_image_tar}}

# Oak Containers Hello World entry point.

oak_containers_hello_world_container_bundle_tar:
    env --chdir=oak_containers_hello_world_container DOCKER_BUILDKIT=0 bash build_container_bundle

oak_containers_hello_world_untrusted_app:
    env cargo build --release --package='oak_containers_hello_world_untrusted_app'

all_oak_containers_binaries: stage0_bin stage1_cpio oak_containers_kernel oak_containers_system_image oak_containers_hello_world_container_bundle_tar oak_containers_hello_world_untrusted_app

# Oak Functions Containers entry point.

oak_functions_containers_container_bundle_tar:
    env --chdir=oak_functions_containers_container DOCKER_BUILDKIT=0 bash build_container_bundle

oak_functions_containers_launcher:
    env cargo build --release --package='oak_functions_containers_launcher'

all_oak_functions_containers_binaries: stage0_bin stage1_cpio oak_containers_kernel oak_containers_system_image oak_functions_containers_container_bundle_tar oak_functions_containers_launcher

# Entry points for Kokoro CI.

kokoro_build_binaries_rust: all_enclave_apps oak_restricted_kernel_bin oak_restricted_kernel_simple_io_bin stage0_bin

kokoro_oak_containers: all_oak_containers_binaries oak_functions_containers_container_bundle_tar
    RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar --package='oak_containers_hello_world_untrusted_app'

kokoro_run_tests:
    RUST_LOG="debug" cargo nextest run --all-targets --hide-progress-bar --workspace --exclude='oak_containers_hello_world_untrusted_app'
