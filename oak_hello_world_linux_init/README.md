<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="docs/oak-logo/svgs/oak-logo-negative.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="docs/oak-logo/svgs/oak-logo.svg?sanitize=true"><img alt="Project Oak Logo" src="docs/oak-logo/svgs/oak-logo.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Initial Process "Hello World" Application

This example "Hello World" application is intended to be run as the initial
process (PID 1) on Linux.

In general, before the rest of the application can run, the initial process must
ensure that the required psuedo file systems are mounted (e.g. `sysfs`) and the
required virtual files are in place (e.g. `/dev/null`). In practice we don't
need any initial setup if we are just logging to the console, so we just have an
empty placeholder initialization section for now.

To test this application as intended, it must be copied onto an
[initial RAM disk](https://en.wikipedia.org/wiki/Initial_ramdisk) (initramfs).
The easiest way to execute the initial RAM disk is to use
[QEMU's direct Linux boot feature](https://qemu-project.gitlab.io/qemu/system/linuxboot.html).

Since the initial RAM disk does not contain a dynamic linker or any other
dependencies the application must be built as a statically linked binary.

## Testing Steps

Note: these steps assume that the commands will be executed from the project
root.

Build the application as a statically linked binary:

```bash
cargo build --release --target=x86_64-unknown-linux-musl \
    --package=oak_hello_world_linux_init
```

Create the initial RAM disk:

```bash
# Create a temporary directory containing the initial workload.
export RAMDIR=$(mktemp -d)
cp --archive target/x86_64-unknown-linux-musl/release/oak_hello_world_linux_init \
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

Note: this assumes an appropiate
[uncompressed Linux kernel ELF binary](/docs/development.md#extracting-vmlinux-from-your-linux-installation)
has been copied to `bin/vmlinux`.

```bash
qemu-system-x86_64 -cpu host -enable-kvm -machine "microvm,acpi=on" -m 1G \
    -nographic -nodefaults -no-reboot -serial stdio -bios "bin/stage0.bin" \
    -fw_cfg "name=opt/stage0/elf_kernel,file=bin/vmlinux" \
    -fw_cfg "name=opt/stage0/initramfs,file=bin/initramfs" \
    -fw_cfg "name=opt/stage0/cmdline,string=console=ttyS0 quiet"
```
