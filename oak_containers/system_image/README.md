<!-- Oak Logo Start -->
<!-- An HTML element is intentionally used since GitHub recommends this approach to handle different images in dark/light modes. Ref: https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax#specifying-the-theme-an-image-is-shown-to -->
<!-- markdownlint-disable-next-line MD033 -->
<h1><picture><source media="(prefers-color-scheme: dark)" srcset="/docs/oak-logo/svgs/oak-containers-negative-colour.svg?sanitize=true"><source media="(prefers-color-scheme: light)" srcset="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"><img alt="Project Oak Containers Logo" src="/docs/oak-logo/svgs/oak-containers.svg?sanitize=true"></picture></h1>
<!-- Oak Logo End -->

# System Image Build Tools

We use this Docker image to build the base system image for Oak Containers.

The bazel-built system image rules layer in freshly-built Oak Containers
binaries onto a pre-created base image. The base iamge is not re-generated on
every run, since it changes very infrequently.

For more information on updating the base image, see `base/README.md`.

# Sysroot

The sysroot provides the libraries and headers used by our CC toolchain. It is
built using `rules_distroless` to ensure reproducibility.

For more details, see [oak_containers/sysroot](../sysroot/README.md).

# Current Issues/Improvements

- There might be a better way to build the base image. It feels a bit hacky, but
  it's working for now.

- The version with nvidia drivers is still largely untested and under
  development.
