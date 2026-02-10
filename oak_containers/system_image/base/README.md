# Base System Image Tools

This directory contains files needed to rebuild the base image used by the
system container.

The base image contains things that rarely change for the image: the base
operating system, network configuration, and service enablements.

This image is used to build the system container image with `oci_rules`,
avoiding the need for Docker when rebuilding a system image container.

To update the base image and push it:

just build-base just push-base

For nvidia;

just build-nvidia-base just push-nvidia-base

For building the sysroot, see: oak_containers/sysroot
