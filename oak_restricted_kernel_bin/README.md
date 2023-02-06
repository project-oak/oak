<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-restricted-kernel-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-restricted-kernel.svg?sanitize=true"><img alt="Project Oak Restricted Kernel Logo" src="/docs/oak-logo/svgs/oak-restricted-kernel.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

This is the binary that needs to be loaded into an enclave to start Restricted
Kernel and run applications targeting Restricted Kernel.

The exact loading mechanism depends on the VMM, but with QEMU (and our stage0
binary), it will be something similar to this:

```bash
$ qemu-system-x86_64
    -machine microvm
    -bios path/to/stage0.bin
    -device loader,file=path/to/oak_restricted_kernel_bin
```
