# Bare-metal Runtime

This experimental runtime is based on the series of blog posts on
https://os.phil-opp.com/. The idea is to reduce the amount of code running
inside a VM-based enclave as far as possible to minimise the TCB.

The initial implementation only tests the ability to boot inside a VM and write
something to the screen.

The stand-alone binary can be built using:

```bash
cargo build --manifest-path=experimental/bare_metal/Cargo.toml \
  --target=experimental/bare_metal/x86_64-bare_metal.json \
  -Zbuild-std=core \
  -Zbuild-std-features=compiler-builtins-mem
```

To be able to boot the stand-alone binary, we need to create a boot image. This
can be done using the cargo `bootimage` tool (see
https://os.phil-opp.com/minimal-rust-kernel/#creating-a-bootimage).

The `bootimage` tool can be installed using:

```bash
cargo install bootimage
```

It also requires `llvm-tools-preview` which can be installed using:

```bash
rustup component add llvm-tools-preview
```

Once these are installed, the boot image can be created using:

```bash
cargo bootimage --manifest-path=experimental/bare_metal/Cargo.toml \
  --target=experimental/bare_metal/x86_64-bare_metal.json \
  -Zbuild-std=core \
  -Zbuild-std-features=compiler-builtins-mem
```

The boot image can be booted using QEMU:

```bash
qemu-system-x86_64 -drive format=raw,file=experimental/bare_metal/target/x86_64-bare_metal/debug/bootimage-bare_metal_runtime.bin
```
