<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# System Image Build Tools

We use this Docker image to build the base system image for Oak Containers.

## Full System Image Tools

`build-old.sh` and `Dockerfile`

Tools for building the Oak Containers system image. The system image contains
the guest Linux distribution and the Orchestrator.

This was the original strategy used for building images. We are keeping it
around for now as reference, as we transition to a docker-free approach.

## Base System Image Tools

`build-base.sh` and `base_image.Dockerfile` and some `BUILD` targets

This directory contains files needed to rebuild the base image used by the
system container.

The base image contains things that rarely change for the image: the base
operating system, network configuration, and service enablements.

This image is used to build the system container image with `oci_rules`,
avoiding the need for Docker when rebuilding a system image container.

To update the base image and push it:

1. ./oak_containers/system_image/build-base.sh
2. ./oak_containers/system_image/push-base.sh vanilla|nvidia

There is also a version of the base image that includes the nvidia drivers.

## Sysroot

We use this to get a full, consistent set of libraries, tools and compilers, and
extract them to make a sysroot. The plan is to plug this sysroot into Bazel to
get a consistent toolchain. This image is not used to run anything at the
moment.

# Current Issues/Improvements

- The bazel version should eventually be full bazel, and not require running any
  scripts.

- There might be a better way to build the base image. It feels a bit hacky, but
  it's working for now.

- The version with nvidia drivers is still largely untested and under
  development.
