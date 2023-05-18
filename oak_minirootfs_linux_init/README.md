<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="../docs/oak-logo/svgs/oak-logo-negative.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="../docs/oak-logo/svgs/oak-logo.svg?sanitize=true"><img alt="Project Oak Logo" src="../docs/oak-logo/svgs/oak-logo.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Shell with Alpine's Mini Root Filesystem

This example shows how to boot into a shell from Oak's stage0 firmware binary.
We can achieve this by simply packaging
[Alpine Linux](https://www.alpinelinux.org)'s mini root filesystem as the
[initial RAM disk](https://en.wikipedia.org/wiki/Initial_ramdisk) (initramfs)
disk with an appropriate init script. The easiest way to execute the initial RAM
disk is to use
[QEMU's direct Linux boot feature](https://qemu-project.gitlab.io/qemu/system/linuxboot.html).

Note: these steps assume that the commands will be executed from the project
root.

First, download an appropriate release of the mini root filesystem from
[Alpine Downloads](https://www.alpinelinux.org/downloads/):

```bash
MINIROOTFS_TGZ=/tmp/alpine-minirootfs.tar.gz
wget https://dl-cdn.alpinelinux.org/alpine/v3.17/releases/x86_64/alpine-minirootfs-3.17.3-x86_64.tar.gz -O ${MINIROOTFS_TGZ}
```

Create the initial RAM disk:

```bash
# Create a temporary directory containing the initial workload.
export RAMDIR=$(mktemp -d)
tar xzvf ${MINIROOTFS_TGZ} -C ${RAMDIR}
cp oak_minirootfs_linux_init/init \
    ${RAMDIR}/init
# Create a compressed CPIO archive.
( cd ${RAMDIR}; find . -print0 \
    | cpio --null --create --format=newc ) \
    | gzip \
    > bin/initramfs
```

Build the Stage 0 Firmware image:

```bash
( cd stage0_bin; cargo build --release; )
objcopy --output-format binary stage0_bin/target/x86_64-unknown-none/release/oak_stage0_bin \
    bin/stage0.bin
```

Execute the initial RAM disk with QEMU:

Note: this assumes that an appropiate
[uncompressed Linux kernel ELF binary](/docs/development.md#extracting-vmlinux-from-your-linux-installation)
has been copied to `bin/vmlinux`. The Linux kernel that comes with Alpine
distribution
[optimized for virtual systems](https://dl-cdn.alpinelinux.org/alpine/v3.17/releases/x86_64/alpine-virt-3.17.3-x86_64.iso)
is suitable.

```bash
qemu-system-x86_64 -cpu host -enable-kvm -machine "microvm" -m 1G \
    -nographic -nodefaults -no-reboot -serial stdio \
    -bios "bin/stage0.bin" \
    -fw_cfg "name=opt/stage0/elf_kernel,file=bin/vmlinux" \
    -fw_cfg "name=opt/stage0/initramfs,file=bin/initramfs" \
    -fw_cfg "name=opt/stage0/cmdline,string=console=ttyS0 quiet"
```

This will get you a shell with access to common utilities.
