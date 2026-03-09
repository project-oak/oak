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
    --port=<port>             # Optional: Port forward (repeatable)
    --headless                # Optional: Run in background
    --enable-snp              # Optional: Enable AMD SEV-SNP
```
