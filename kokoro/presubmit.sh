#!/usr/bin/env bash

./scripts/docker_pull

ls -l /dev/kvm
# Fix the permissions of /dev/kvm.
readonly KVM_GID="$(getent group kvm | cut -d: -f3)"
sudo chown "$USER:$KVM_GID" /dev/kvm
ls -l /dev/kvm
./scripts/docker_run ls -l /dev/kvm

./scripts/docker_run ./scripts/xtask build-oak-functions-server-variants
./scripts/docker_run ./scripts/xtask run-vm-test
