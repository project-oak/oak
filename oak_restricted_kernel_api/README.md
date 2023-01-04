<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-restricted-kernel-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-restricted-kernel.svg?sanitize=true"><img alt="Project Oak Restricted Kernel Logo" src="/docs/oak-logo/svgs/oak-restricted-kernel.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Oak Restricted Kernel API

This crate contains Rust wrappers for the Oak Restricted Kernel interface.

Users of Oak Restricted Kernel should only depend on this crate, and not the
kernel itself. (Note that unfortunately we're not quite there yet with the
isolation, but that's the future goal.)
