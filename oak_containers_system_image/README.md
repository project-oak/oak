<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# System Image Build Tools

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

1. ./oak_containers_system_image/build-base.sh
2. bazel run --stamp oak_containers_system_image:push_base

## Bazel-Based System Image Tools

`just oak_containers_system_image` and some `BUILD` targets

How this works:

1. We expect that `build-base.sh` has already been run, pushed an image, and the
   WORKSPACE points to that image, as described above.

2. The script will build the two needed binaries using cargo. Once those crates
   are bazelified, we can make them proper targets.

3. The syslogd binary is patched. We can eventually craft some sort of bazel
   rule to do this.

4. `oci_image` target pulls the previously built base, and layers the two
   binaries onto it.

5. `oci_runtime_bundle` exports the bundle to a tarball that we can use.

# Current Issues/Improvements

- The bazel version should eventually be full bazel, and not require running any
  scripts.

- There might be a better way to build the base image. It feels a bit hacky, but
  it's working for now.

- When umoci exports a runtime bundle, the files are under ./rootfs. But the
  base image built with the old way has all files in the top level. We'll
  probably need to mimic that structure. There are lots of ways to do this, but
  it's not clear what the most correct one is.
