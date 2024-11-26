# The expectation is that we build `base_image.Dockerfile` before this one.
# hadolint ignore=DL3007
FROM oak-containers-sysimage-base:latest

ARG LINUX_KERNEL_VERSION

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# We need to enable `contrib` for `nvidia-support`.
RUN sed -i -e '/^Components: main/cComponents: main contrib' \
    /etc/apt/sources.list.d/debian.sources

RUN apt-get --yes update \
    && apt-get install --yes --no-install-recommends \
    curl gpg ca-certificates

RUN curl -O -L https://developer.download.nvidia.com/compute/cuda/repos/debian12/x86_64/cuda-keyring_1.1-1_all.deb \
    && dpkg -i cuda-keyring_1.1-1_all.deb \
    && rm -f cuda-keyring_1.1-1_all.deb

# See https://docs.nvidia.com/datacenter/cloud-native/container-toolkit/latest/install-guide.html#installing-with-apt
RUN curl -fsSL https://nvidia.github.io/libnvidia-container/gpgkey | gpg --dearmor -o /usr/share/keyrings/nvidia-container-toolkit-keyring.gpg \
    && curl -s -L https://nvidia.github.io/libnvidia-container/stable/deb/nvidia-container-toolkit.list | \
    sed 's#deb https://#deb [signed-by=/usr/share/keyrings/nvidia-container-toolkit-keyring.gpg] https://#g' | \
    tee /etc/apt/sources.list.d/nvidia-container-toolkit.list

RUN apt-get --yes update \
    && apt-get install --yes --no-install-recommends \
    nvidia-driver nvidia-smi \
    libcuda1 nvidia-container-toolkit \
    # Stuff to build kernel (will be purged later, see below)
    libc6-dev flex bison build-essential bc cpio libncurses5-dev libelf-dev libssl-dev dwarves debhelper-compat rsync \
    # Cleanup
    && apt-get clean \
    && rm --recursive --force /var/lib/apt/lists/*

# Generate /etc/cdi/nvidia.json for the orchestrator.
RUN systemctl enable nvidia-ctk.service

COPY target/linux-${LINUX_KERNEL_VERSION}.tar.xz /tmp
COPY target/minimal.config /tmp

RUN tar --directory=/tmp --extract --file /tmp/linux-${LINUX_KERNEL_VERSION}.tar.xz \
    && cp /tmp/minimal.config /tmp/linux-${LINUX_KERNEL_VERSION}/.config \
    && make --directory=/tmp/linux-${LINUX_KERNEL_VERSION} -j"$(nproc)" bindeb-pkg \
    && dpkg --install /tmp/linux-headers-${LINUX_KERNEL_VERSION}_${LINUX_KERNEL_VERSION}-1_amd64.deb \
    && dkms build -m nvidia-current -v "$(dpkg-query --showformat='${source:Upstream-Version}' --show nvidia-driver)" -k ${LINUX_KERNEL_VERSION} \
    && dkms install -m nvidia-current -v "$(dpkg-query --showformat='${source:Upstream-Version}' --show nvidia-driver)" -k ${LINUX_KERNEL_VERSION} \
    && rm -rf /tmp/linux-${LINUX_KERNEL_VERSION} /tmp/linux-${LINUX_KERNEL_VERSION}.tar.xz /tmp/minimal.config \
    && apt-get --yes purge libc6-dev flex bison build-essential bc cpio libncurses5-dev libelf-dev libssl-dev dwarves debhelper-compat rsync \
    && apt-get --yes autoremove

# Remove a bunch of stuff we know we won't need.
RUN apt-get --yes purge openssl autoconf cpp gcc groff-base libgssapi-krb5-2 man-db \
    && apt-get --yes autoremove
# Technically this leaves the packages in a broken state as they're dependencies of nvidia-driver;
# however, as we can reasonably predict we will never rebuild kernel modules without rebuilding the
# whole system image we don't really need the compiler in there.
# It's entirely possible that:
# (a) we could force-purge more packages without any ill effects and
# (b) the current list includes something we actually need but don't know yet.
RUN  dpkg --purge --force-all \
    binutils-common libbinutils libctf0 libgprofng0 binutils-x86-64-linux-gnu binutils \
    libxml2 libicu72 libperl5.36 perl libdpkg-perl perl-modules-5.36 dpkg-dev dkms libz3-4 \
    libasan8 libtsan2 liblsan0 libubsan1 xz-utils make \
    libllvm15 gcc-12 cpp-12 libgcc-12-dev \
    nvidia-kernel-dkms linux-headers-${LINUX_KERNEL_VERSION} \
    xserver-xorg-video-nvidia xkb-data keyboard-configuration xserver-common xserver-xorg-core \
    libfreetype6 libxfont2
