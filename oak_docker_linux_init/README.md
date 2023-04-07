<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="../docs/oak-logo/svgs/oak-logo-negative.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="../docs/oak-logo/svgs/oak-logo.svg?sanitize=true"><img alt="Project Oak Logo" src="../docs/oak-logo/svgs/oak-logo.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Running a Docker container from stage0

This example shows how to run a Docker container from Oak's stage0 firmware
binary. We can achieve this by simply extracting the filesystem of the Docker
container and packaging it as the
[initial RAM disk](https://en.wikipedia.org/wiki/Initial_ramdisk) (initramfs)
disk with an appropriate init binary. The easiest way to execute the initial RAM
disk is to use
[QEMU's direct Linux boot feature](https://qemu-project.gitlab.io/qemu/system/linuxboot.html).

Note: these steps assume that the commands will be executed from the project
root.

Suppose that we want to run the
[`hello-world:latest`](https://hub.docker.com/_/hello-world) Docker image, we
can convert it to a initramfs with the
[docker_to_initramfs.sh](docker_to_initramfs.sh) script as follows:

```bash
sh oak_docker_linux_init/docker_to_initramfs.sh hello-world:latest bin/initramfs
```

Build the Stage 0 Firmware image:

```bash
( cd stage0; cargo build --release; )
objcopy --output-format binary stage0/target/x86_64-unknown-none/release/oak_stage0 \
    bin/stage0.bin
```

Execute the initial RAM disk with QEMU:

Note: this assumes that an appropiate
[uncompressed Linux kernel ELF binary](/docs/development.md#extracting-vmlinux-from-your-linux-installation)
has been copied to `bin/vmlinux`.

```bash
qemu-system-x86_64 -cpu host -enable-kvm -machine "microvm" -m 1G \
    -nographic -nodefaults -no-reboot -serial stdio \
    -bios "bin/stage0.bin" \
    -fw_cfg "name=opt/stage0/elf_kernel,file=bin/vmlinux" \
    -fw_cfg "name=opt/stage0/initramfs,file=bin/initramfs" \
    -fw_cfg "name=opt/stage0/cmdline,string=console=ttyS0 quiet"
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
