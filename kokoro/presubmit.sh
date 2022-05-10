#!/usr/bin/env bash

# On Kokoro instances /dev/kvm is owned by root:root. Let's fix the permissions
# so that it's owned by group `kvm` as our scripts expect it to.
readonly KVM_GID="$(getent group kvm | cut -d: -f3)"
sudo chown "$USER:$KVM_GID" /dev/kvm

./scripts/docker_pull

./scripts/docker_run ./scripts/xtask build-oak-functions-server-variants
./scripts/docker_run ./scripts/xtask run-vm-test
