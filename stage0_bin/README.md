<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-stage0-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-stage0.svg?sanitize=true"><img alt="Project Oak Stage0 Logo" src="/docs/oak-logo/svgs/oak-stage0.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

Oak stage0 is a purposefully minimal (trusted) firmware for virtual machines
that can boot 64-bit Linux(-compatible) kernels (bzImage).

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
- loading and parsing bzImage kernels
- [the 64-bit Linux boot protocol](https://www.kernel.org/doc/html/v5.6/x86/boot.html#id1)
  (boot parameters structure)

We do not support block devices or network devices, and that is intentional.

Only x86-64 is supported.

Stage0 also does not provide any BIOS or EFI services. It's designed to boot a
kernel, after which stage0 is no longer needed.

## Compiling and running

The easiest way to create the BIOS blob is to use the `just` command:

```shell
just stage0_bin
```

The resulting file (`artifacts/binaries/stage0_bin`) should be exactly
`BIOS_SIZE` (defined in `layout.ld`) in size. The size of the BIOS image should
not exceed 2 MiB.

To use the binary, pass it to `qemu -bios`; for example:

```shell
qemu-system-x86_64 -cpu host -enable-kvm -machine "microvm,acpi=on" -m 1G \
  -nographic -nodefaults -no-reboot -serial stdio \
  -bios "artifacts/binaries/stage0_bin"
```

## Loading a kernel

Stage 0 loads the kernel over the `fw_cfg` device. It expects that the kernel is
compatible with the Linux `bzImage` format.

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
- [Alioth](https://github.com/google/alioth) is an experimental lightweight VMM.
  Written in Rust; supports SEV, SEV-ES, and SEV-SNP with stage0 firmware
  ([doc](https://github.com/google/alioth/blob/main/docs/coco.md)).
