<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-stage-0-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-stage-0.svg?sanitize=true"><img alt="Project Oak Logo" src="/docs/oak-logo/svgs/oak-stage-0.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

This is a minimal firmware for use with QEMU and compatible VMMs that puts the
CPU into the desired state, enters long mode, retrieves required configuration
information (E820 memory layout and ACPI tables) and jumps into the kernel entry
point.

The E820 memory map and ACPI tables are read using the
[QEMU Firmware Configuration (fw_cfg)](https://www.qemu.org/docs/master/specs/fw_cfg.html)
device.

To create the BIOS blob, you need to turn it into a headerless file with
`objcopy` after the binary was built:

```shell
cargo build --release
objcopy --output-target binary target/x86_64-unknown-none/release/oak_stage0 \
    target/x86_64-unknown-none/release/stage0.bin
```

This can also be done in one step using cargo-binutils:

```shell
cargo objcopy --release -- --output-target binary \
    target/x86_64-unknown-none/release/stage0.bin
```

The resulting `stage0.bin` should be exactly `BIOS_SIZE` (defined in
`layout.ld`) in size. The size of the BIOS image should not exceed 1 MB.

To use the binary, pass it to `qemu -bios`; for example:

```shell
qemu-system-x86_64 -nodefaults -nographic -no-reboot -machine microvm -bios stage0.bin
```
