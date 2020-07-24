# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/debian/snapshot/tags
ARG debian_snapshot=buster-20200327
FROM debian/snapshot:${debian_snapshot}

# Set the SHELL option -o pipefail before RUN with a pipe in.
# See https://github.com/hadolint/hadolint/wiki/DL4006
SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Uncomment the RUN below if the default snapshot package manager is slow.
# Please not that this might cause issues and affects reproducible builds,
# so only use for development.
# RUN echo \
#  deb [arch=amd64] http://ukdebian.mirror.anlx.net/debian buster main non-free contrib\
# > /etc/apt/sources.list

RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  build-essential \
  ca-certificates \
  curl \
  libssl-dev \
  pkg-config \
  unzip \
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

# Install Protobuf compiler.
ARG protobuf_version=3.11.4
ARG protobuf_sha256=6d0f18cd84b918c7b3edd0203e75569e0c8caecb1367bbbe409b45e28514f5be
ARG protobuf_dir=/usr/local/protobuf
ARG protobuf_temp=/tmp/protobuf.zip
ENV PATH "${protobuf_dir}/bin:${PATH}"
RUN curl --location https://github.com/protocolbuffers/protobuf/releases/download/v${protobuf_version}/protoc-${protobuf_version}-linux-x86_64.zip > ${protobuf_temp} \
  && sha256sum --binary ${protobuf_temp} && echo "${protobuf_sha256} *${protobuf_temp}" | sha256sum --check \
  && unzip ${protobuf_temp} -d ${protobuf_dir} \
  && rm ${protobuf_temp} \
  && protoc --version

# Install rustup.
ARG rustup_dir=/usr/local/cargo
ENV RUSTUP_HOME ${rustup_dir}
ENV CARGO_HOME ${rustup_dir}
ENV PATH "${rustup_dir}/bin:${PATH}"
RUN curl --location https://sh.rustup.rs > /tmp/rustup \
  && sh /tmp/rustup -y --default-toolchain=none \
  && chmod a+rwx ${rustup_dir} \
  && rustup --version

# Install Rust toolchain.
# We currently need the nightly version in order to be able to compile some of the examples.
# See https://rust-lang.github.io/rustup-components-history/ for how to pick a version that supports
# the appropriate set of components.
ARG rust_version=nightly-2020-06-10
RUN rustup toolchain install ${rust_version} \
  && rustup default ${rust_version}

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install musl target for Rust (for statically linked binaries).
RUN rustup target add x86_64-unknown-linux-musl
