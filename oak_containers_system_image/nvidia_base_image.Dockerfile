# The expectation is that we build `base_image.Dockerfile` before this one.
# hadolint ignore=DL3007
FROM oak-containers-sysimage-base:latest

ARG LINUX_KERNEL_VERSION

# We need to enable `contrib` for `nvidia-support`.
RUN sed -i -e '/^Components: main/cComponents: main contrib' \
    /etc/apt/sources.list.d/debian.sources

RUN apt-get --yes update \
    && apt-get install --yes --no-install-recommends \
    curl ca-certificates

RUN curl -O -L https://developer.download.nvidia.com/compute/cuda/repos/debian12/x86_64/cuda-keyring_1.1-1_all.deb \
    && dpkg -i cuda-keyring_1.1-1_all.deb \
    && rm -f cuda-keyring_1.1-1_all.deb

RUN apt-get --yes update \
    && apt-get install --yes --no-install-recommends \
    nvidia-driver nvidia-smi \
    # Stuff to build kernel (will be purged later, see below)
    libc6-dev flex bison build-essential bc cpio libncurses5-dev libelf-dev libssl-dev dwarves debhelper-compat rsync \
    # Cleanup
    && apt-get clean \
    && rm --recursive --force /var/lib/apt/lists/*

COPY target/linux-${LINUX_KERNEL_VERSION}.tar.xz /tmp
COPY target/minimal.config /tmp

RUN tar --directory=/tmp --extract --file /tmp/linux-${LINUX_KERNEL_VERSION}.tar.xz \
    && cp /tmp/minimal.config /tmp/linux-${LINUX_KERNEL_VERSION}/.config \
    && make --directory=/tmp/linux-${LINUX_KERNEL_VERSION} bindeb-pkg \
    && dpkg --install /tmp/linux-headers-${LINUX_KERNEL_VERSION}_${LINUX_KERNEL_VERSION}-1_amd64.deb \
    && dkms build -m nvidia-current -v "$(dpkg-query --showformat='${source:Upstream-Version}' --show nvidia-driver)" -k ${LINUX_KERNEL_VERSION} \
    && dkms install -m nvidia-current -v "$(dpkg-query --showformat='${source:Upstream-Version}' --show nvidia-driver)" -k ${LINUX_KERNEL_VERSION} \
    && rm -rf /tmp/linux-${LINUX_KERNEL_VERSION} /tmp/linux-${LINUX_KERNEL_VERSION}.tar.xz /tmp/minimal.config \
    && apt-get --yes purge libc6-dev flex bison build-essential bc cpio libncurses5-dev libelf-dev libssl-dev dwarves debhelper-compat rsync \
    && apt-get --yes autoremove

