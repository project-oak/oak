<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Kernel Build Tool

Tools to build a Linux Kernel version that can be used as the guest kernel for
Oak Containers.

# Updating the Linux Kernel Version

The Linux kernel is built using Nix to help with reproducibility. The kernel
version is specified in `flake.nix` in the root.

If the Linux configuration options have changed significantly between versions
the config file must be updated. This can be done by manually building the
kernel using the existing config file and the new version's source code. Choose
appropriate values for any new configuration options and then copy the updated
config file back to the source tree after the build has completed.
