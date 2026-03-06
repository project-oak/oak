# Oak Containers Application Base

## Overview

This directory contains files for configuring the base image for the Oak
Containers apps managed directly in the Oak Repository.

It's also available to use if you're depending on Oak to create your own runtime
bundles for Oak Containers.

## Quick Guide

The easiest way to get started is to use our `app_bundle` macro in your `BUILD`
file:

```python
load("//oak_containers/app_base:defs.bzl", "app_bundle")

app_bundle(
    name = "bundle",
    binary = ":my_binary",
    args = ["--arg1", "val1"],
    env = {"MY_ENV": "value"},
)
```

This will produce a tarball target named `bundle` that is compatible with the
Oak Containers Orchestrator. Standard environment variables like `PATH`, `HOME`,
`TERM`, and `SSL_CERT_FILE` are provided by default but can be overridden in the
`env` dictionary.

## Components

### `app_bundle` Macro

The `app_bundle` macro generates an OCI-like bundle tarball. The resulting
tarball contains:

1. `config.json`: A configuration file at the root, generated from a template.
   It specifies the entrypoint (your binary), default capabilities, and mounts.
2. `rootfs/`: A directory containing the filesystem.
   - Your application binary is placed at `/usr/local/bin/` by default.
   - Base system files are included from the `base_image`.

### `app_base.yaml`

This file defines the base image using `rules_distroless`. It specifies the
Debian snapshot and the minimal set of packages (`base-files`) included in the
default base image. This ensures a small, reproducible, and secure starting
point for applications.

### `oak_app_config` Rule

If you are managing your filesystem (rootfs) independently but still want to
generate an Oak-compatible `config.json`, you can use the `oak_app_config` rule
directly:

```python
load("//oak_containers/app_base:defs.bzl", "oak_app_config")

oak_app_config(
    name = "my_config",
    args = ["/path/to/my/binary", "--my-arg"],
    env = {
        "MY_VAR": "my_value",
        "HOME": "/custom/home",
    },
)
```

This rule handles:

- Merging your environment variables with Oak's defaults.
- Generating the JSON structure required by the Orchestrator's runtime (runc).
- Setting default capabilities and mounts that are consistent with Oak's
  security model.

## More Information

### Oak Containers Runtime Bundles

Since we call the project Oak Containers, the initial expectation a newcomer has
is that you should provide some sort of container deliverable to Oak Containers.
But what our runtime expects is actually an already-unpacked OCI image.

Luckily, this is a very simple format; in fact, it's even simpler than an image:
It's simply a tarball containing:

- A `config.json` file at the root.
- A directory (typically `rootfs/`) containing the entire root filesystem of the
  container.

The path to the filesystem directory is defined in the `config.json` file (under
the `root.path` property). By default, our tools use `rootfs/`.

The `config.json` file provides instructions on how the system should be
configured, including the entry point for your application. Since most use cases
share a standard configuration, the only dynamic need is typically populating
the entry point and environment.

### Why Not Use Images?

In the past, we've had discussions in various contexts about the possibility of
simply supporting container image types directly in Oak Containers, having our
runtime unpack them before running them.

While this is definitely feasible, we've decided against it, for a few reasons:

1. Additional logic and maintance overhead in the Oak Containers Orchestrator.
2. Additional overhead when loading an image - now the runtime will have to
   unpack it, adding even more time to the container startup.
3. Fewer transformations of the measured runtime bundle. We are unpacking your
   tarball, fixing the permissions, and calling runc.
4. The `rules_distroless` approach is more "in the spirit" of the Oak Project.
   We want to encourage simple, reproducible approaches to creating the runtime
   bundles that run in Oak Containers.

### Manage Your Runtime Bundles Your Way

While we provide convenient tools for common Oak Containers use cases, there's
no requirement to use them:

- You can still use docker to create an image and export its runtime bundle
- You can use Bazel's rules_oci along with a tool like umoci to create and then
  unpack images.
- You can manually craft your own image using whatever sources you'd like.
