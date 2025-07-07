<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# Oak Functions Standalone

An Oak Functions standalone binary. This binary relies on the Oak Session
library to establish an encrypted channel with clients. Unlike the Oak Functions
flavors that run on the Restricted Kernel or Oak Containers, this service does
not require an Oak Functions Launcher to configure the binary's environment. The
environment setup is instead done at the startup of the server.

This server binary implements the gRPC service specified in
oak/proto/oak_functions/standalone/oak_functions_session.proto and is intended
to run on a Linux-based environment.

As an example, the main binary performs basic temperature lookups from a limited
set of latitude and longitude entries.

To run: `bazel run //oak_functions_standalone:oak_functions_standalone`
