# The expectation is that we build `base_image.Dockerfile` before this one.
# hadolint ignore=DL3007
FROM oak-containers-sysimage-base:latest

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
    cuda-toolkit-12-4 nvidia-driver \
    # Cleanup
    && apt-get clean \
    && rm --recursive --force /var/lib/apt/lists/*