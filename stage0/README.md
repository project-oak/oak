# stage0

This is -- or, rather, will be -- a minimal firmware for use with QEMU that just
enters long mode with no extra features.

To create the BIOS blob, you need to turn it into a headerless file with
`objcopy`:

```shell
objcopy --output-format binary target/x86_64-unknown-none/{debug,release}/oak_stage0 stage0.bin
```

The resulting `stage0.bin` should be exactly `BIOS_SIZE` (defined in
`layout.ld`) in size. The size of the BIOS image should not exceed 1 MB.

To use the binary, pass it to `qemu -bios`; for example:

```shell
qemu-system-x86_64 -nodefaults -nographic -no-reboot -machine microvm -bios stage0.bin
```
