# Oak Restricted Kernel Wrapper

A minimal wrapper for the Oak Restricted kernel that is compatible with the
[Linux x86-64 boot protocol v2.15](https://www.kernel.org/doc/html/v6.5/arch/x86/boot.html).
This wrapper allows the Stage 0 virtual firmware to boot the Oak Restricted
Kernel in the same way as a compressed 64-bit Linux kernel.

The wrapper is responsible for parsing the payload (the Oak Restricted Kernel)
as an ELF file, laying it out in memory and doing any required relocations.

To build it, run the following in the workspace root:

```bash
just oak_restricted_kernel_wrapper_virtio_console_channel
```
