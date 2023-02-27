#!/usr/bin/env bash

# On Kokoro instances /dev/kvm, /dev/vhost-vsock and /dev/vsock are owned by root:root.
# Set the permissions so that these are owned by the `kvm` group as our scripts expect it to be.
readonly KVM_GID="$(getent group kvm | cut -d: -f3)"
sudo chown "$USER:$KVM_GID" /dev/kvm

sudo /etc/init.d/docker stop
sudo mv /var/lib/docker /tmpfs/
sudo ln -s /tmpfs/docker /var/lib/docker
sudo /etc/init.d/docker start

export CI=kokoro

export RUST_BACKTRACE=1
export RUST_LOG=debug

./scripts/docker_pull
./scripts/docker_run xtask --scope=all run-cargo-tests

cp ./target/nextest/default/junit.xml "$KOKORO_ARTIFACTS_DIR/"
ls -als "$KOKORO_ARTIFACTS_DIR"
