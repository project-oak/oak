#!/bin/bash

set -e
mkdir -p target

# build the orchestrator binary
cargo build --package="oak_containers_orchestrator" --release --target="x86_64-unknown-linux-musl" -Z unstable-options --out-dir="./target"
cargo build --package="oak_containers_syslogd" --release -Z unstable-options --out-dir="./target"
patchelf --set-interpreter /lib64/ld-linux-x86-64.so.2 ./target/oak_containers_syslogd

docker build . --tag oak-containers-system-image
# We need to actually create a container, otherwise we won't be able to use `docker export` that gives us a filesystem image.
# (`docker save` creates a tarball which has all the layers separate, which is _not_ what we want.)
readonly NEW_DOCKER_CONTAINER_ID="$(docker create oak-containers-system-image:latest)"

docker export "$NEW_DOCKER_CONTAINER_ID" > target/image.tar
ls -lah target/image.tar
xz --force target/image.tar

docker rm "$NEW_DOCKER_CONTAINER_ID"
