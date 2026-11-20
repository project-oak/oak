# Linux boot data structures

This crate contains (a subset of) the data structures needed to boot the Linux
kernel, which are of interest to someone who wants to implement a bootloader (or
a kernel compatible with the Linux boot protocol).

The data structures themselves were first generated with `bindgen` as follows:

```shell
bindgen /usr/include/asm/bootparam.h
```

and then hand-modified to make then more Rust-y (fix names, use `bitfield!`
etc).

## EFI

`oak_linux_boot_params::efi` provides the structures needed to pass a minimal
post-`ExitBootServices()` EFI memory map and Linux unaccepted-memory bitmap via
`BootParams::efi_info`.

## References

- [UEFI Specification, Version 2.11](https://uefi.org/specs/UEFI/2.11/)
- [ACPI Specification, Version 6.6](https://uefi.org/specs/ACPI/6.6/05_ACPI_Software_Programming_Model.html#finding-the-rsdp-on-uefi-enabled-systems)
- [Linux x86 Boot Protocol](https://docs.kernel.org/arch/x86/boot.html)
- [Linux x86 Zero Page](https://docs.kernel.org/arch/x86/zero-page.html)
