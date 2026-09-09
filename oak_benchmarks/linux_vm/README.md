# Linux VM Tools

Tools for creating and running Linux VMs for benchmark testing.

## Prerequisites

```bash
sudo apt install libguestfs-tools qemu-system-x86
```

## Bazel Macro (Recommended)

Use the `vm_disk_image` macro to define VM images in BUILD files.

### Example

In `oak_benchmarks/linux_enclave_app/BUILD`:

```python
load("//oak_benchmarks/linux_vm:defs.bzl", "vm_disk_image")

vm_disk_image(
    name = "linux_enclave_image",
    binary = ":linux_enclave_app",
    command = "/opt/app/linux_enclave_app --serve 5000",
)
```

### Build

```bash
bazel build //oak_benchmarks/linux_enclave_app:linux_enclave_image
```

### Run Benchmarks

The `vm_disk_image` macro automatically generates a `<name>_run` target that
boots the VM and runs the benchmark in a single command.

```bash
bazel run //oak_benchmarks/linux_enclave_app:linux_enclave_image_run -- --benchmark=sha256
```

#### 2. Manual Run

For manual interaction or custom scripts, you can use `run_vm.sh` directly.

```bash
./oak_benchmarks/linux_vm/run_vm.sh \
    --image=bazel-bin/oak_benchmarks/linux_enclave_app/linux_enclave_image.qcow2 \
    --port=5000
```

## Shell Scripts

### `prepare_image.sh`

For ad-hoc image creation with explicit file paths:

```bash
./oak_benchmarks/linux_vm/prepare_image.sh \
    --binary=/path/to/my_app \
    --base-image=/path/to/debian.qcow2 \
    --output=/tmp/my-vm.qcow2 \
    --command="/opt/app/my_app --port 5000"
```

### `run_vm.sh`

Runs a VM image:

```bash
./oak_benchmarks/linux_vm/run_vm.sh \
    --image=<path>            # Required: qcow2 image
    --port=<port>             # Optional: Port forward (repeatable, user net only)
    --net=<user|tap>          # Optional: Network mode (default: user)
    --headless                # Optional: Run in background
    --vm-type=<type>          # Optional: default, sev, sev-es or sev-snp
    --bios=<path>             # Optional: firmware, required by a confidential guest
    --cbitpos=<n>             # Optional: encryption bit position (default: 51)
```

A confidential guest needs firmware carrying a SEV metadata table, and its NIC
is given `iommu_platform=on`, without which the guest kernel refuses to probe
it. `--cbitpos` is the one SEV value QEMU checks against the host: 51 is right
for Milan and Genoa, 47 for Naples and Rome.

**No `--vm-type` other than `default` has been run on SEV hardware.** The QEMU
arguments follow AMD's reference invocation rather than a guest that booted.

## Networking

**`--net=user` (default)** is QEMU's user-mode stack, SLIRP: a TCP
implementation inside the QEMU process, reached through `--port` forwards on
loopback. It needs no privileges and works anywhere, which is why it is the
default, but it is far slower than a real NIC. A benchmark that crosses it is
measuring SLIRP as much as the guest, so treat it as a pessimistic Linux
baseline, not as _the_ Linux number.

**`--net=tap`** attaches a pre-created persistent tap device with the in-kernel
vhost datapath, so the kernel moves packets between the tap and the guest's
virtqueues and QEMU only sets the path up. This is what a deployment uses.

One image serves both: `vm_disk_image(extra_ip = ...)` adds a static address
alongside DHCP, unused under user networking and the only way in under tap,
where nothing serves DHCP.

### One-off host setup for `--net=tap`

Creating a tap device is privileged, using one you already own is not, so this
is run once by hand and QEMU stays unprivileged afterwards.

```bash
sudo ip tuntap add dev oaktap0 mode tap user "${USER}"
sudo ip addr add 198.18.0.1/30 dev oaktap0
sudo ip link set oaktap0 up
sudo setfacl -m u:"${USER}":rw /dev/vhost-net
```

- `mode tap` is layer 2, which QEMU needs to present a virtio-net NIC.
  `user ${USER}` makes the device yours, so QEMU can attach without
  `CAP_NET_ADMIN`.
- The name is not `oak0`, which `oak_containers/launcher` and
  `oak_functions_test_utils` already use. Those create their tap inside an
  `unshare --net` namespace and tear it down with it; this one is persistent and
  lives in the host namespace, so it gets a name that cannot collide with them.
- `198.18.0.0/15` is the RFC 2544 benchmarking range, which must never appear in
  production routing, so a directly-connected route for it cannot shadow
  anything real. The `/30` holds `.1` for the host and `.2` for the guest.
- Without `/dev/vhost-net` QEMU emulates the NIC in userspace, a milder version
  of what `--net=tap` exists to avoid, so `run_vm.sh` refuses to start rather
  than measure the wrong thing. `setfacl` grants one user and leaves the owner,
  group and mode alone; prefer it to `chmod`.

The device reads `DOWN` until QEMU attaches: a persistent tap with no process
holding it open has no carrier. Expected.

To undo:

```bash
sudo ip link del oaktap0
sudo setfacl -x u:"${USER}" /dev/vhost-net
```

Neither survives a reboot anyway — a persistent tap persists across QEMU exits,
not across boots, and an ACL on a `devtmpfs` node is recreated each boot.
