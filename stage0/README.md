# stage0

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
objcopy --output-format binary target/x86_64-unknown-none/release/oak_stage0 \
    target/x86_64-unknown-none/release/stage0.bin
```

This can also be done in one step using cargo-binutils:

```shell
cargo objcopy --release -- --output-format binary \
    target/x86_64-unknown-none/release/stage0.bin
```

The resulting `stage0.bin` should be exactly `BIOS_SIZE` (defined in
`layout.ld`) in size. The size of the BIOS image should not exceed 1 MB.

To use the binary, pass it to `qemu -bios`; for example:

```shell
qemu-system-x86_64 -nodefaults -nographic -no-reboot -machine microvm -bios stage0.bin
```
