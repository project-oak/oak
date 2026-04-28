# Base System Image Tools

This directory contains files needed to rebuild the base image used by the
system container.

The base image contains things that rarely change for the image: the base
operating system, network configuration, and service enablements.

This image is used to build the system container image with `oci_rules`,
avoiding the need for Docker when rebuilding a system image container.

To update the base image and push it:

```bash
just containers system-image
just containers push-system-image
```

For nvidia;

```bash
just containers nvidia-system-image
just containers push-nvidia-system-image
```

For building the sysroot, see: oak_containers/sysroot
