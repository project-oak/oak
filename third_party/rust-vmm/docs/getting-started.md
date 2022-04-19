# Getting Started with the Reference VMM

## Contents

- [Getting Started with the Reference VMM](#getting-started-with-the-reference-vmm)
  - [Contents](#contents)
  - [Prerequisites](#prerequisites)
    - [OS & Hypervisor](#os--hypervisor)
  - [Build the Reference VMM](#build-the-reference-vmm)
  - [Run the Reference VMM](#run-the-reference-vmm)
    - [Kernel](#kernel)
    - [Devices](#devices)
      - [Block Device](#block-device)
    - [Putting It All Together](#putting-it-all-together)

## Prerequisites

### OS & Hypervisor

Currently, the reference VMM runs on Linux **x86_64** hosts, using the **KVM**
hypervisor. To make sure KVM is accessible to your user, run:

```bash
[ -r /dev/kvm ] && [ -w /dev/kvm ] && echo "OK" || echo "FAIL"
```

To grant your user access to KVM, either:

1. If you have the ACL package for your distro installed:

    ```bash
    sudo setfacl -m u:${USER}:rw /dev/kvm
    ```

    or

2. If your distribution uses the `kvm` group to manage access to `/dev/kvm`:

    ```bash
    [ $(stat -c "%G" /dev/kvm) = kvm ] && sudo usermod -aG kvm ${USER}
    ```

    Then log out and back in.

## Build the Reference VMM

To build the reference VMM from source, you need to have the Rust compiler and
`cargo` installed on your system. The following toolchains are supported:

- `x86_64-unknown-linux-gnu` (Linux with `glibc`, **default**)
- `x86_64-unknown-linux-musl` (Linux with `musl libc`)

As the reference VMM does not yet have any compile-time features, building it
is as simple as:

```bash
cargo build [--release]
```

This will produce a binary called `vmm-reference` in the `cargo` build
directory (default: `target/${toolchain}/${mode}`, where mode can be `debug` or
`release`).

## Run the Reference VMM

### Kernel

To build a kernel for the reference VMM to boot, check out the scripts in
[resources/kernel](../resources/kernel).

- [`make_kernel_busybox_image.sh`](../resources/kernel/make_kernel_busybox_image.sh)
  builds an ELF or bzImage kernel with a baked-in initramfs running
  [Busybox](https://busybox.net/). It uses a stripped-down
  [kernel config](../resources/kernel/microvm-kernel-initramfs-hello-x86_64.config)
  and a statically linked [config](../resources/kernel/busybox_static_config)
  for the Busybox initramfs.

  Example:

  ```bash
  sudo ./make_kernel_busybox_image.sh -f elf -k vmlinux-hello-busybox -w /tmp/kernel
  ```

  produces a binary image called `vmlinux-hello-busybox` in the `/tmp/kernel`
  directory. Root privileges are needed to create device nodes.

  Run `./make_kernel_busybox_image.sh` with no arguments to see the help.

- [`make_kernel_image_deb.sh`](../resources/kernel/make_kernel_image_deb.sh)
  builds an ELF or bzImage kernel compatible with Ubuntu 20.04 from a
  stripped-down
  [kernel config](../resources/kernel/microvm-kernel-5.4-x86_64.config), as
  well as `.deb` packages containing the Linux kernel image and modules, to be
  installed in the guest. By default, the script downloads the `.deb` packages
  from an
  [official Ubuntu mirror](http://security.ubuntu.com/ubuntu/pool/main/l/linux-hwe-5.4),
  but it can build them from the same sources as the kernel instead. Users can
  opt in for this behavior by setting the `MAKEDEB` environment variable
  before running the script.

  Example:

  ```bash
  ./make_kernel_image_deb.sh -f bzimage -j 2 -k bzimage-focal -w /tmp/ubuntu-focal
  ```

  produces a binary image called `bzimage-focal` in the `/tmp/ubuntu-focal`
  directory. It downloads the `linux-modules` and `linux-image-unsigned`
  packages and places them inside the kernel source directory within
  `/tmp/ubuntu-focal` (the exact location is displayed at the end).

  Run `./make_kernel_image_deb.sh` with no arguments to see the help.

For more usage examples, see the
[Buildkite pipeline](../.buildkite/deps-pipeline.yml) that calls these scripts
as part of the CI.

### Devices

The reference VMM only supports a serial console device for now. This section
will be expanded as other devices are added. Block devices are in the works.

#### Block Device

To build a block device with a root filesystem in it containing an OS for the
reference VMM, check out the scripts in [resources/disk](../resources/disk).

- [`make_rootfs.sh`](../resources/disk/make_rootfs.sh) builds a 1 GiB disk
  image containing an `ext4` filesystem with an Ubuntu 20.04 image.

  Example:

  ```bash
  sudo resources/disk/make_rootfs.sh -d /tmp/ubuntu-focal/deb -w /tmp/ubuntu-focal
  ```

  produces a file called `rootfs.ext4` inside `/tmp/ubuntu-focal` containing
  the Ubuntu 20.04 image and the kernel image installed from the `.deb`
  packages expected in `/tmp/ubuntu-focal/deb`. At the very least, the OS needs
  the `linux-image` and `linux-modules` packages. These can either be
  downloaded or built from sources. See [this section][#kernel] for examples on
  how to acquire these packages using scripts from this repo.

  Root privileges are needed to manage mountpoints.

### Putting It All Together

Once all the prerequisites are met, the reference VMM can be run either
directly through `cargo`, passing on its specific
[command line arguments](../README.md#cli-reference), or after building it with
`cargo build`.

```wrap
cargo run --release --            \
    --memory size_mib=1024        \
    --kernel path=${KERNEL_PATH}  \
    --vcpu num=1
```

```wrap
cargo build --release
target/release/vmm-reference      \
    --memory size_mib=1024        \
    --kernel path=${KERNEL_PATH}  \
    --vcpu num=1
```
