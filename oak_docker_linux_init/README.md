<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="../docs/oak-logo/svgs/oak-logo-negative.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="../docs/oak-logo/svgs/oak-logo.svg?sanitize=true"><img alt="Project Oak Logo" src="../docs/oak-logo/svgs/oak-logo.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Running a Docker container from stage0

This example shows how to run a Docker container from Oak's stage0 firmware
binary. We can achieve this by preparing an
[initial RAM disk](https://en.wikipedia.org/wiki/Initial_ramdisk) (initramfs)
that sets up the environment and launches the entry point of the docker image.
Once we have the appropriate initial RAM disk, the easiest way to execute it is
to use
[QEMU's direct Linux boot feature](https://qemu-project.gitlab.io/qemu/system/linuxboot.html).

**Note:** these steps assume that the commands will be executed from the project
root.

## Prepare the initial RAM disk (initramfs)

To run a Docker image on top of stage0 firmware binary, the key idea is to
extract the filesystem from the Docker image and package it either as an
initramfs image or a chroot tree.

### Docker filesystem as the initial RAM disk

If the Docker image is self sufficient and does not need any drivers, we can
simply extract the filesystem of the Docker image and package it as an initramfs
image. This is generally suitable for docker images that were built from
scratch.

Suppose that we want to run the
[`hello-world:latest`](https://hub.docker.com/_/hello-world) Docker image, we
can convert it to a initramfs with the
[docker_to_initramfs.sh](docker_to_initramfs.sh) script as follows:

```bash
sh oak_docker_linux_init/docker_to_rootfs.sh -d hello-world:latest -o bin/initramfs
```

Note that if you simply want to extract the filesystem in the Docker image
without packaging it as an initramfs image, you can omit the `-o` option and use
the `-r` option to specify the destination for the extracted filesystem as
follows:

```bash
sh oak_docker_linux_init/docker_to_rootfs.sh -d hello-world:latest -r /tmp/docker_rootfs
```

Note that the script `docker_to_rootfs.sh` puts an `init` binary at the root of
the directory, which launches the docker entry point after setting up the
necessary environment. You can use this `init` binary as the `/init` for the
initramfs or as the initial binary when you `chroot` to the filesystem extracted
from the Docker image.

### Docker filesystem as a chroot tree

If the Docker image requires drivers and additional setup, we can have custom
Docker launcher that is packaged as an initramfs image and then launch the
docker container. We will use an [Alpine Linux](https://www.alpinelinux.org/)
distribution for the purposes of this prototype. Ideally, we want to implement
the Docker launcher from scratch and build a custom Linux kernel with all
drivers, but the Alpine Linux distribution will help illustrate and derisk the
changes needed to support Docker on top of Oak stage0.

We will need the following packages from
[Alpine Linux Downloads](https://www.alpinelinux.org/downloads/) Page:

- [Alpine Minirootfs](https://dl-cdn.alpinelinux.org/alpine/v3.17/releases/x86_64/alpine-minirootfs-3.17.3-x86_64.tar.gz):
  for an initial filesystem.
- [Alpine Netboot](https://dl-cdn.alpinelinux.org/alpine/v3.17/releases/x86_64/alpine-netboot-3.17.3-x86_64.tar.gz):
  for a Linux kernel and drivers.

Download the necesary files:

```bash
OAK_DOCKER_PREP_DIR=$(mktemp -d)
MINIROOTFS_TGZ="${OAK_DOCKER_PREP_DIR}/alpine-minirootfs.tar.gz"
wget https://dl-cdn.alpinelinux.org/alpine/v3.17/releases/x86_64/alpine-minirootfs-3.17.3-x86_64.tar.gz \
 -O "${MINIROOTFS_TGZ}"

NETBOOT_TGZ="${OAK_DOCKER_PREP_DIR}/alpine-netboot.tar.gz"
wget https://dl-cdn.alpinelinux.org/alpine/v3.17/releases/x86_64/alpine-netboot-3.17.3-x86_64.tar.gz \
 -O "${NETBOOT_TGZ}"

EXTRACT_VMLINUX="${OAK_DOCKER_PREP_DIR}/extract-vmlinux.sh"
wget https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/plain/scripts/extract-vmlinux \
 -O "${EXTRACT_VMLINUX}"

```

Extract the initramfs from netboot:

```bash
NETBOOT_INITRAMFS="${OAK_DOCKER_PREP_DIR}/netboot-initramfs"
tar xzvf "${NETBOOT_TGZ}" boot/initramfs-virt -O > "${NETBOOT_INITRAMFS}"
```

Also extract the corresponding compressed kernel and extract the vmlinux file.
You will need the
[extract-vmlinux](https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git/plain/scripts/extract-vmlinux)
script from the kernel source code.

```bash
NETBOOT_COMPRESSED_KERNEL="${OAK_DOCKER_PREP_DIR}/netboot-vmlinuz"
NETBOOT_VMLINUX="${OAK_DOCKER_PREP_DIR}/netboot-vmlinux"

tar xzvf "${NETBOOT_TGZ}" boot/vmlinuz-virt -O > "${NETBOOT_COMPRESSED_KERNEL}"
sh "${EXTRACT_VMLINUX}" "${NETBOOT_COMPRESSED_KERNEL}" > "${NETBOOT_VMLINUX}"
```

You might want to copy the kernel to the `bin/` at the root of Oak's workspace
to use as the Linux kernel when launching QEMU later:

```bash
cp ${NETBOOT_VMLINUX} bin/vmlinux
```

Note that you need to extract the kernel from so that it will be compatible with
the drivers we will extract from the Alpine's initramfs file.

Build the initramfs with minirootfs, drivers, and a Docker image
([`tensorflow/tensorflow`](https://hub.docker.com/r/tensorflow/tensorflow/)
here):

```bash
sh oak_docker_linux_init/prepare_docker_launcher_initramfs.sh \
  -k ${NETBOOT_VMLINUX} \
  -i ${NETBOOT_INITRAMFS} \
  -m ${MINIROOTFS_TGZ} \
  -o bin/initramfs \
  -d tensorflow/tensorflow
```

To create an initramfs that will simply boot into a working shell, you can skip
the `-d` option:

```bash
sh oak_docker_linux_init/prepare_docker_launcher_initramfs.sh \
  -k ${NETBOOT_VMLINUX} \
  -i ${NETBOOT_INITRAMFS} \
  -m ${MINIROOTFS_TGZ} \
  -o bin/initramfs
```

## Build the Stage 0 Firmware image

```bash
( cd stage0; cargo build --release; )
objcopy --output-format binary stage0/target/x86_64-unknown-none/release/oak_stage0 \
    bin/stage0.bin
```

## Execute the initial RAM disk with QEMU with virtual net device

Note: this assumes that an appropiate
[uncompressed Linux kernel ELF binary](/docs/development.md#extracting-vmlinux-from-your-linux-installation)
has been copied to `bin/vmlinux`.

```bash
qemu-system-x86_64 -cpu host -enable-kvm -machine "microvm" -m 8G \
    -nographic -nodefaults -no-reboot -serial stdio \
    -bios "bin/stage0.bin" \
    -fw_cfg "name=opt/stage0/elf_kernel,file=${NETBOOT_VMLINUX}" \
    -fw_cfg "name=opt/stage0/initramfs,file=bin/initramfs" \
    -fw_cfg "name=opt/stage0/cmdline,string=console=ttyS0 quiet" \
    -netdev user,ipv6=off,id=user \
    -device virtio-net-device,netdev=user
```

Note that you can forward ports from host device to the guest device by using
the `hostfwd` option in QEMU. For example, to forward tcp port 8888 from host to
guest, you replace the `netdev` option on the above command line as follows:

```text
  -netdev user,ipv6=off,id=user,hostfwd=tcp::8888-:8888
```

After initializing the rootfs, the `/init` in the initramfs will execute the
`CMD` or `ENTRYPOINT` from the Docker image.

_Note:_ the initramfs can only be at most half the size of the machine's memory.
You may get an error like '`Initramfs unpacking failed: write error`' if the
size of the memory is not big enough. Increase the size of the virtual machine's
memory should usually fix this error.

_Note:_ the compressed initramfs image should also fit within the first 1G along
with the Linux kernel. Otherwise, this approach of using initramfs will not
work.

# Examples

## Serve Jupyter notebooks with a Tensorflow runtime

Build initramfs:

```bash
sh oak_docker_linux_init/prepare_docker_launcher_initramfs.sh \
  -k ${NETBOOT_VMLINUX} \
  -i ${NETBOOT_INITRAMFS} \
  -m ${MINIROOTFS_TGZ} \
  -o bin/initramfs \
  -d tensorflow/tensorflow:nightly-jupyter
```

Launch QEMU with network, where tcp port `8888` is forwarded from host to guest:

```bash
qemu-system-x86_64 -cpu host -enable-kvm -machine "microvm" -m 8G \
    -nographic -nodefaults -no-reboot -serial stdio \
    -bios "bin/stage0.bin" \
    -fw_cfg "name=opt/stage0/elf_kernel,file=${NETBOOT_VMLINUX}" \
    -fw_cfg "name=opt/stage0/initramfs,file=bin/initramfs" \
    -fw_cfg "name=opt/stage0/cmdline,string=console=ttyS0 quiet" \
    -netdev user,ipv6=off,id=user,hostfwd=tcp::8888-:8888 \
    -device virtio-net-device,netdev=user
```
