<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-stage0-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-stage0.svg?sanitize=true"><img alt="Project Oak Stage0 Logo" src="/docs/oak-logo/svgs/oak-stage0.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

Oak stage0 is a purposefully minimal (trusted) firmware for virtual machines
that can boot 64-bit Linux(-compatible) ELF kernels.

The motivating example for having a minimal firmware is secure virtual machines,
such as virtual machines running under AMD SEV-SNP or Intel TDX, where it is
beneficial to minimize the amount of code that needs to be trusted (that is,
running inside the virtual machine).

To that end, stage0 intentionally tries to limit itself to the minimum amount of
actions needed to set up the machine, preferring to do as much work in
memory-safe Rust as possible. Unfortunately we're still dealing with low-level
machine state here, so we've had to resort to some assembly code and some
`unsafe` code.

## Features

We target the QEMU `microvm` machine (and compatible VMMs), and support:

- [QEMU `fw_cfg`](https://www.qemu.org/docs/master/specs/fw_cfg.html) device
  (for obtaining memory information, ACPI tables etc)
- serial port (for logging)
- AMD SEV, SEV-ES and SEV-SNP (setting encrypted bit in the page tables and
  validating guest physical memory)
- loading and parsing ELF kernels
- [the 64-bit Linux boot protocol](https://www.kernel.org/doc/html/v5.6/x86/boot.html#id1)
  (boot parameters structure)

We do not support block devices or network devices, and that is intentional.

Only x86-64 is supported.

Stage0 also does not provide any BIOS or EFI services. It's designed to boot a
kernel, after which stage0 is no longer needed.

## Compiling and running

To create the BIOS blob, you need to turn it into a headerless file with
`objcopy` after the stage0 binary was built:

```shell
cargo build --release
objcopy --output-target binary target/x86_64-unknown-none/release/oak_stage0_bin \
    target/x86_64-unknown-none/release/oak_stage0.bin
```

This can also be done in one step using cargo-binutils:

```shell
cargo objcopy --release -- --output-target binary \
    target/x86_64-unknown-none/release/oak_stage0.bin
```

The resulting `oak_stage0.bin` should be exactly `BIOS_SIZE` (defined in
`layout.ld`) in size. The size of the BIOS image should not exceed 1 MB.

To use the binary, pass it to `qemu -bios`; for example:

```shell
qemu-system-x86_64 -nodefaults -nographic -no-reboot -machine microvm \
    -bios target/x86_64-unknown-none/release/oak_stage0.bin
```

## Loading a kernel

There are two options for loading the kernel: either get the VMM to load it into
guest memory before the VM even starts, or let stage0 load the kernel from
`fw_cfg`. Both approaches have their benefits and drawbacks.

**Note**: the kernel has to be an ELF file! If you want to use Linux, use the
`extract-vmlinux` script to create the uncompressed `vmlinux` image from the
`bzImage` file.

### Option 1: pre-loading the kernel

You can use the QEMU `loader` device to load a kernel into memory:

```shell
qemu-system-x86_64 [...] -device loader,file=/path/to/kernel
```

As long as the file is in ELF format, QEMU will lay out the binary in guest
memory based on the instructions in the ELF file.

Notes:

- The `loader` device does not ask the PSP to encrypt the memory under SEV, so
  this will only work with no memory encryption enabled.
- stage0 will assume that there is an ELF header at address `0x20_0000` (2 MiB).
  If no ELF header is found at that address, stage0 will just blindly jump to
  that address, expecting it to be executable.

### Option 2: loading the kernel via `fw_cfg`

We also support loading the kernel (and an initial ramdisk) via two custom
`fw_cfg` entries:

```shell
qemu-system-x86_64 [...] -fw_cfg name=opt/stage0/elf_kernel,file=/path/to/kernel \
                         -fw_cfg name=opt/stage0/initramfs,file=/path/to/initramfs \
                         -fw_cfg name=opt/stage0/cmdline,string=console=ttyS0
```

Unfortunately we had to implement custom `fw_cfg` entries; the standard
`-kernel` flag won't work as QEMU may load files into guest memory, but it will
not ask the PSP to encrypt the memory. If we don't provide a `-kernel` flag,
QEMU will reject `-initrd` and `-append` flags; thus, we had to reimplement
those as well.

This approach is supported under SEV and SEV-ES. (Probably also SEV-SNP, but the
public releases of QEMU do not support SEV-SNP yet.)

## Internals

### Memory layout

Stage0 maps the first 1 GiB of physical memory using identity mapping before
handing control over to the kernel. The stage0 binary itself is mapped into
memory just below the end of 4 GiB address space, like any other BIOS ROM.

We explicitly reserve the SMBIOS entry table memory range (0xF0000-0xFFFFF) to
indicate that Stage0 initializes this range.

```text
               |                      ...                       |
 0x1_0000_0000 +------------------------------------------------+ 4GiB
               |               Stage 0 ROM Image                |
   0xFFFE_0000 +------------------------------------------------+ 4GiB - 128MiB
               |                    PCI Hole                    |
   0xC000_0000 +------------------------------------------------+ 3GiB
               |                  Unmapped RAM                  |
   0x4000_0000 +------------------------------------------------+ 1GiB
               |                                                |
                                      ...
               |                                                |
               +------------------------------------------------+
               |                                                |
               |               Restricted Kernel                |
               |                                                |    Kernel
     0x20_1000 +------------------------------------------------+ <- Entry Point
               |          Restricted Kernel ELF Header          |
     0x20_0000 +------------------------------------------------+ 2MiB
               |                                                |
     0x10_0000 +------------------------------------------------+ 1MiB
               |    Reserved SMBIOS entry point table memory    |
      0xF_0000 +------------------------------------------------+ 960KiB
               |                    BIOS Hole                   |
      0xA_0000 +------------------------------------------------+ 640KiB
               |     Extended BIOS Data Area (ACPI Tables)      |
      0x8_0000 +------------------------------------------------+ 512KiB
               |             Stage 0 Stack and Heap             |
               | (Includes Secrets and CPUID pages on SEV-SNP)  |
        0x1000 +------------------------------------------------+ 4KiB
               |                 Unmapped Page                  |
           0x0 +------------------------------------------------+
```

### AMD SEV-SNP Memory validation

The Linux kernel and the Oak restricted kernel both assume that the firmware
will validate all (or at least most) of the guest-physical memory before jumping
into the kernel (by calling the PVALIDATE instruction).

Because legacy code may scan the SMBIOS region (even if marked as reserved in
the E820 table), we pvalidate this region to prevent crashes.

We don't have to PVALIDATE the Stage 0 ROM image range, since that memory was
already set in the appropriate validated state by the Secure Processor before
launching the guest VM.

```text
               |     PVALIDATEd up to end of physical memory    |
 0x1_0000_0000 +------------------------------------------------+ 4GiB
               |    Stage 0 ROM Image (PVALIDATE not needed)    |
   0xFFFE_0000 +------------------------------------------------+ 4GiB - 128MiB
               |                   PVALIDATEd                   |
     0x10_0000 +------------------------------------------------+ 1MiB
               |   PVALIDATEd SMBIOS entry point table memory   |
      0xF_0000 +------------------------------------------------+ 960KiB
               |                    BIOS Hole                   |
      0xA_0000 +------------------------------------------------+ 640KiB
               |      PVALIDATEd by bootstrap assembly code     |
           0x0 +------------------------------------------------+
```

## Future work

- Support for Intel TDX

## Related projects

There are several other projects in similar firmware space that may be of
interest:

- [Rust Hypervisor Firmware](https://github.com/cloud-hypervisor/rust-hypervisor-firmware)
  This project implements what could be referred to a "second half" of a more
  generic firmware: it expects to be booted via PVH, and can load a kernel off a
  block device. The main target VMM is Cloud Hypervisor, but it also supports
  QEMU. (Note that QEMU relies on SeaBIOS and an option ROM to provide PVH boot
  support.) Does not support SEV.
- [SeaBIOS](https://github.com/qemu/seabios) is a fully-featured BIOS
  implementation, written in C. This is the default firmware QEMU uses. Does not
  support SEV.
- [EDK2 / OVMF](https://github.com/tianocore/edk2) is a fully-featured UEFI
  firmware that can be used with QEMU. Written in C; supports everything,
  including SEV, SEV-ES, SEV-SNP, and the kitchen sink.
