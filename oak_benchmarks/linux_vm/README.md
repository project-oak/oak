# Linux VM Tools

Scripts for creating and running Linux VMs for benchmark testing.

## Prerequisites

Install these packages before using the scripts:

```bash
sudo apt install libguestfs-tools qemu-system-x86
```

## Quick Start

> ⚠️ **IMPORTANT**: Always build with `-c opt` for benchmarks!

```bash
# 1. Download the base image
./oak_benchmarks/linux_vm/download_base_image.sh ~/Downloads

# 2. Build your application (RELEASE MODE - required for benchmarks!)
bazel build -c opt //oak_benchmarks/linux_app

# 3. Create VM image with your app
# IMPORTANT: Use the explicit k8-opt path to ensure release binary
./oak_benchmarks/linux_vm/prepare_image.sh \
    --base-image=~/Downloads/debian-12-nocloud-amd64.qcow2 \
    --binary=bazel-out/k8-opt/bin/oak_benchmarks/linux_app/linux_app \
    --output=/tmp/benchmark-vm.qcow2 \
    --command="/opt/app/linux_app --server --port=5000" \
    --port=5000

# 4. Run the VM
# When prompted for login, type `root`
./oak_benchmarks/linux_vm/run_vm.sh --image=/tmp/benchmark-vm.qcow2 --port=5000
```

## Scripts

### `download_base_image.sh`

Downloads the Debian 12 "nocloud" base image with SHA512 verification.

```bash
./oak_benchmarks/linux_vm/download_base_image.sh [output_directory]
```

### `prepare_image.sh`

Creates a VM image with an application binary pre-installed.

```bash
./oak_benchmarks/linux_vm/prepare_image.sh \
    --base-image=<path>       # Required: Debian nocloud qcow2
    --binary=<path>           # Required: Application binary
    --output=<path>           # Required: Output image path
    --command=<cmd>           # Optional: ExecStart for systemd service (include args like --server)
    --service-name=<name>     # Optional: systemd service name (default: app)
    --port=<port>             # Optional: Port for documentation (default: 5000)
    --install-path=<path>     # Optional: Where to install (default: /opt/app)
```

### `run_vm.sh`

Runs a VM with various options.

```bash
./oak_benchmarks/linux_vm/run_vm.sh \
    --image=<path>            # Required: qcow2 image
    --memory=<size>           # Optional: Memory (default: 1G)
    --cpus=<n>                # Optional: CPU count (default: 2)
    --port=<port>             # Optional: Port forward (repeatable)
    --interactive             # Optional: Attach console (default)
    --headless                # Optional: Run in background
    --enable-snp              # Optional: Enable AMD SEV-SNP
```

## How It Works

The `prepare_image.sh` script:

1. Copies the binary to a staging directory
2. Uses `guestfish` to inject the binary into the VM image without booting it
3. Creates a systemd service for auto-start on boot
