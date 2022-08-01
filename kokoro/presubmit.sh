#!/usr/bin/env bash

# Kokoro requires us to manually load the kernel modules required for vsock
# Ref: https://g3doc.corp.google.com/security/bedebox/g3doc/requirements.md?cl=head#vhostvhost-vsock-kernel-module-vs-vmware
sudo rmmod vmw_vsock_virtio_transport_common
sudo rmmod vmw_vsock_vmci_transport
sudo rmmod vsock
sudo modprobe vhost_vsock

# On Kokoro instances /dev/kvm, /dev/vhost-vsock and /dev/vsock are owned by root:root.
# Set the permissions so that these are owned by the `kvm` group as our scripts expect it to be.
readonly KVM_GID="$(getent group kvm | cut -d: -f3)"
sudo chown "$USER:$KVM_GID" /dev/kvm
sudo chown "$USER:$KVM_GID" /dev/vhost-vsock
sudo chown "$USER:$KVM_GID" /dev/vsock

./scripts/docker_pull

./scripts/docker_run ./scripts/xtask build-oak-functions-server-variants
./scripts/docker_run ./scripts/xtask run-launcher-test
