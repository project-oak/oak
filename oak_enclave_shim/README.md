<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-restricted-kernel-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-restricted-kernel.svg?sanitize=true"><img alt="Project Oak Restricted Kernel Logo" src="/docs/oak-logo/svgs/oak-restricted-kernel.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

The enclave shim is a thin wrapper around Oak Restricted Kernel that makes it
possible to embed a standalone application binary into a loadable enclave
binary.

Usage:

1. Compile the intended application binary (for example, Oak Functions)
2. Compile the shim with the needed kernel features
3. Embed the application binary into the shim binary:
   `objcopy --update_section .payload=path/to/application_binary path/to/shim_binary path/to/output_enclave_binary`
4. Load the resulting enclave binary into the secure enclave.
