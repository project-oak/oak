<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# System Image Build Tools

## Full System Image Tools

`build.sh` and `Dockerfile`

Tools for building the Oak Containers system image. The system image contains
the guest Linux distribution and the Orchestrator.

## Base System Image Tools

`build-base.sh` and `base_iamge.Dockerfile`

This directory contains files needed to rebuild the base image used by the
system container.

The base image contains things that rarely change for the image: the base
operating system, network configuration, and service enablements.

This image is used to build the system container image with `oci_rules`,
avoiding the need for Docker when rebuilding a system image container.
