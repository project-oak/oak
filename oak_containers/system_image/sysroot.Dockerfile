# Builds a Docker image from which we can extract a sysroot.

# At the moment we don't use this image to run anything - only to copy out
# the sysroot (essesntially, C libraries and tools). The goal is to plug this
# sysroot into Bazel C toolchains so as to align compiler and library versions
# at build time (Bazel) and at runtime (e.g. containers system image).

# The expectation is that we build `base_image.Dockerfile` before this one.
# hadolint ignore=DL3007
FROM oak-containers-sysimage-base:latest

ARG LINUX_KERNEL_VERSION

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

RUN apt-get --yes update \
    && apt-get install --yes --no-install-recommends \
    libc6-dev libstdc++-12-dev \
    flex bison build-essential bc cpio libncurses5-dev libelf-dev libssl-dev dwarves debhelper-compat rsync \
    kmod \
    # Cleanup
    && apt-get clean \
    && rm --recursive --force /var/lib/apt/lists/*

COPY target/linux-${LINUX_KERNEL_VERSION}.tar.xz /tmp
COPY target/minimal.config /tmp

RUN tar --directory=/tmp --extract --file /tmp/linux-${LINUX_KERNEL_VERSION}.tar.xz \
    && cp /tmp/minimal.config /tmp/linux-${LINUX_KERNEL_VERSION}/.config \
    && make --directory=/tmp/linux-${LINUX_KERNEL_VERSION} -j"$(nproc)" bindeb-pkg \
    && dpkg --install /tmp/linux-headers-${LINUX_KERNEL_VERSION}_${LINUX_KERNEL_VERSION}-1_amd64.deb \
    && rm -rf /tmp/linux-${LINUX_KERNEL_VERSION} /tmp/linux-${LINUX_KERNEL_VERSION}.tar.xz /tmp/minimal.config

# hadolint ignore=SC2114
RUN rm --recursive /usr/share
RUN rm --recursive /usr/src
# hadolint ignore=SC2114
RUN rm --recursive /var
