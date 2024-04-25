#!/bin/bash

set -o xtrace
set -o errexit
set -o nounset
set -o pipefail

readonly SCRIPTS_DIR="$(dirname "$0")"

cd "$SCRIPTS_DIR"

mkdir --parent target

# build the orchestrator binary
cargo build --package=oak_containers_orchestrator --profile=release-lto --target=x86_64-unknown-linux-musl -Z unstable-options --out-dir=./target
cargo build --package=oak_containers_syslogd --release -Z unstable-options --out-dir=./target

# We need to patch the binary to set the interpreter to the correct location, but we can't do it in-place, as that would
# confuse cargo. Therefore we copy the binary to a new location and patch that.
cp ./target/oak_containers_syslogd ./target/oak_containers_syslogd_patched

# When built under nix the interpreter points to some Nix-specific location that doesn't exist on a regular Linux host, therefore
# we need to manually patch the binary to set it back to the normal regular location.
patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 ./target/oak_containers_syslogd_patched

# Fix the file permissions that will be loaded into the system image, as Git doesn't track them.
# Unfortunately we can't do it in Dockerfile (with `COPY --chown`), as that requires BuildKit.
chmod --recursive a+rX files/

docker build . --tag=oak-containers-system-image:latest
# We need to actually create a container, otherwise we won't be able to use `docker export` that gives us a filesystem image.
# (`docker save` creates a tarball which has all the layers separate, which is _not_ what we want.)
readonly NEW_DOCKER_CONTAINER_ID="$(docker create oak-containers-system-image:latest)"

docker export "$NEW_DOCKER_CONTAINER_ID" > target/image-old.tar
ls -lah target/image-old.tar
# Hack, as Docker doesn't give us a `/etc/hosts` which means `localhost` won't resovle.
tar --append --file=target/image.tar --directory=files etc/hosts
xz --force target/image-old.tar

docker rm "$NEW_DOCKER_CONTAINER_ID"
