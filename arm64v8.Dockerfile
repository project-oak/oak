# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/debian/snapshot/tags
ARG debian_snapshot=buster-20201012
# Use a fixed version of Bazel.
ARG bazel_version=3.0.0

# This is a workaround for issues using BuildKit + Mirrors, i.e. GCB
# TARGETARCH and friends are only defined in a BuildKit environment,
# We provide them manually here in hope that BuildKit on GCB will be
# upgraded, and will enable direct use of these.
ARG TARGETARCH=arm64
ARG TARGETVARIANT=v8
ARG TARGETPLATFORM=linux/arm64v8 

# Build up the static musl toolchain using cross-build
FROM debian:${debian_snapshot} AS musl-build-arm64v8
WORKDIR /musl
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  apt-transport-https \
  build-essential \
  curl \
  git \
  openjdk-11-jdk \
  python \
  python3 \
  unzip \
  wget \
  zip \
  zlib1g-dev \
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*
RUN git clone https://github.com/richfelker/musl-cross-make.git
WORKDIR /musl/musl-cross-make
# Set the target
RUN echo "TARGET=aarch64-linux-musl" > config.mak
# Build the target - output ends up in 'output'
RUN make install

# Bootstrap Bazel Stage
FROM debian:${debian_snapshot} AS bazel-bootstrap-arm64v8
WORKDIR /bazel/bazel-dist
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  apt-transport-https \
  build-essential \
  curl \
  openjdk-11-jdk \
  python \
  python3 \
  unzip \
  zip \
  zlib1g-dev \
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*
ARG bazel_version
RUN curl --location -k https://github.com/bazelbuild/bazel/releases/download/${bazel_version}/bazel-${bazel_version}-dist.zip  -o bazel-${bazel_version}-dist.zip
RUN  unzip bazel-${bazel_version}-dist.zip
RUN  BUILD_DATE="$(date --utc --date="@${SOURCE_DATE_EPOCH:-$(date +%s)}" +%Y-%m-%d)" EXTRA_BAZEL_ARGS="--host_javabase=@local_jdk//:jdk" bash ./compile.sh 

# Rebuild Bazel using bootstrap stage
FROM bazel-bootstrap-arm64v8 AS bazel-build-arm64v8
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  git 
WORKDIR /bazel/bazel-build
ARG bazel_version
RUN git clone -b ${bazel_version}  https://github.com/bazelbuild/bazel
WORKDIR /bazel/bazel-build/bazel 
COPY --from=bazel-bootstrap-arm64v8 /bazel/bazel-dist/output/bazel ./bazel-bootstrap
RUN SOURCE_DATE_EPOCH=$(git log -1 --format=%ct) ./bazel-bootstrap build //src:bazel --compilation_mode=opt

# Main Oak Build - We do not re-use the Bazel intermediates here
FROM debian:${debian_snapshot} AS oak-arm64v8

# Set the SHELL option -o pipefail before RUN with a pipe in.
# See https://github.com/hadolint/hadolint/wiki/DL4006
SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Uncomment the RUN below if the default snapshot package manager is slow.
# Please note that this might cause issues and affects reproducible builds,
# so only use for development.
# RUN echo \
#  deb http://ukdebian.mirror.anlx.net/debian buster main non-free contrib\
# > /etc/apt/sources.list

# Getting curl and certificates dependecies.
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  apt-transport-https \
  build-essential \
  cabal-install \
  ca-certificates \
  clang-tidy \
  curl \
  # Emscripten uses cmake
  cmake \
  # Bootstrapping Haskell Compiler
  ghc \ 
  git \
  gnupg2 \
  gnupg-agent \
  libfl2 \
  libncurses5 \
  libssl-dev \
  musl-tools \
  netbase \
  pkg-config \
  procps \
  python3 \
  python3-six \
  python3-distutils \
  shellcheck \
  software-properties-common \
  vim \
  xml2 \
  # `unzip` and `zlib1g-dev` are needed for Bazel.
  unzip \
  zlib1g-dev \
  # Cleanup
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/* \
  # Print version of various installed tools.
  && git --version \
  && shellcheck --version

# Install a version of docker CLI.
RUN curl --fail --silent --show-error --location https://download.docker.com/linux/debian/gpg | apt-key add -
RUN echo "deb https://download.docker.com/linux/debian buster stable"  > /etc/apt/sources.list.d/backports.list \
  && apt-get --yes update \
  && apt-get install --no-install-recommends --yes docker-ce-cli \
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

# Use a later version of clang-format from buster-backports.
RUN echo 'deb http://deb.debian.org/debian buster-backports main' > /etc/apt/sources.list.d/backports.list \
  && apt-get --yes update \
  && apt-get install --no-install-recommends --yes clang-format-8 \
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/* \
  && ln --symbolic --force clang-format-8 /usr/bin/clang-format


# [aarch64] Pull in the bootstrapped Bazel, unfortunately Bazel's Debian
# packaging is currently amd64 specific 
COPY --from=bazel-build-arm64v8 /bazel/bazel-build/bazel/bazel-out/aarch64-opt/bin/src/bazel /usr/bin/bazel

# [aarch64] Pull in the musl compiler
COPY --from=musl-build-arm64v8 /musl/musl-cross-make/output /usr

# Install the necessary binaries and SDKs, ordering them from the less frequently changed to the
# more frequently changed.
# See https://docs.docker.com/develop/develop-images/dockerfile_best-practices/#leverage-build-cache.

# Match the NPM version used elsewhere. Emscripten usually pulls this version in, however emscripten is broken on aarch64.
ARG node_version=12.18.1
ARG node_temp=/tmp/node.tar.xz
ARG NODE_ROOT=/usr/local/node
ENV PATH "${NODE_ROOT}/bin:${PATH}"
RUN mkdir -p ${NODE_ROOT} \
  && curl --show-error --location https://nodejs.org/dist/v${node_version}/node-v${node_version}-linux-arm64.tar.xz > ${node_temp} \
  && tar --extract --file=${node_temp} --directory=${NODE_ROOT} --strip-components=1 \
  && rm ${node_temp} \
  && npm version

  #  && sha256sum --binary ${node_temp} && echo "${node_sha256} *${node_temp}" | sha256sum --check \

# Install Go.
ARG golang_version=1.14.6
ARG golang_sha256=291bccfd7d7f1915599bbcc90e49d9fccfcb0004b7c62a2f5cdf0f96a09d6a3e
ARG golang_temp=/tmp/golang.tar.gz
ARG TARGETARCH
ENV GOROOT /usr/local/go
ENV GOPATH ${HOME}/go
ENV PATH "${GOROOT}/bin:${PATH}"
ENV PATH "${GOPATH}/bin:${PATH}"
# Enable Go module behaviour even in the presence of GOPATH; this way we can specify precise
# versions via `go get`.
# See https://dev.to/maelvls/why-is-go111module-everywhere-and-everything-about-go-modules-24k
ENV GO111MODULE on
RUN mkdir --parents ${GOROOT} \
  && curl --location https://dl.google.com/go/go${golang_version}.linux-${TARGETARCH}.tar.gz > ${golang_temp} \
  && sha256sum --binary ${golang_temp} && echo "${golang_sha256} *${golang_temp}" | sha256sum --check \
  && tar --extract --gzip --file=${golang_temp} --directory=${GOROOT} --strip-components=1 \
  && rm ${golang_temp} \
  && go version

# Install embedmd (Markdown snippet embedder) (via Go).
# https://github.com/campoy/embedmd
RUN go get github.com/campoy/embedmd@97c13d6 \
  && embedmd -v

# Install liche (Markdown link checker) (via Go).
# https://github.com/raviqqe/liche
RUN go get github.com/raviqqe/liche@f57a5d1 \
  && liche --version

# Install prettier and markdownlint (via Node.js).
# This will use the Node version installed by emscripten.
# https://prettier.io/
# https://github.com/igorshubovych/markdownlint-cli
ARG prettier_version=2.1.1
ARG prettier_plugin_toml_version=0.3.1
ARG markdownlint_version=0.22.0
RUN npm install --global \
  prettier@${prettier_version} \
  prettier-plugin-toml@${prettier_plugin_toml_version} \
  markdownlint-cli@${markdownlint_version} \
  && prettier --version \
  && markdownlint --version

# Install hadolint.
# https://github.com/hadolint/hadolint
# TODO: Add hadolint version
# TODO: Build cabal as separate base image as per Bazel
# Debian's Stack is not recent enough in the Buster distribution to build or run Hadolint.
# We use Cabal to build it from scratch.
# This requires a rebuild of cabal in the process to update to 3.2.0
# We also have to work around the Hadolint installer not
# honoring --prefix, by using the older v1 install process.
RUN cabal update \
  && cabal install --prefix=/usr --bindir=/usr/bin --symlink-bindir=/usr/bin --global Cabal cabal-install \
  && cabal user-config update \
  && cabal v1-install --prefix=/usr --bindir=/usr/bin --symlink-bindir=/usr/bin --global hadolint

# Install buildifier.
ARG bazel_tools_version=2.2.1
ARG buildifier_sha256=731a6a9bf8fca8a00a165cd5b3fbac9907a7cf422ec9c2f206b0a76c0a7e3d62
ARG buildifier_dir=/usr/local/buildifier/bin
ARG buildifier_bin=${buildifier_dir}/buildifier
RUN go get github.com/bazelbuild/buildtools/buildifier@"${bazel_tools_version}"

# Install Protobuf compiler.
ARG protobuf_version=3.11.4
# ARG protobuf_sha256=6d0f18cd84b918c7b3edd0203e75569e0c8caecb1367bbbe409b45e28514f5be
#  && sha256sum --binary ${protobuf_temp} && echo "${protobuf_sha256} *${protobuf_temp}" | sha256sum --check \
ARG protobuf_dir=/usr/local/protobuf
ARG protobuf_temp=/tmp/protobuf.zip
ENV PATH "${protobuf_dir}/bin:${PATH}"
RUN curl --location https://github.com/protocolbuffers/protobuf/releases/download/v${protobuf_version}/protoc-${protobuf_version}-linux-aarch_64.zip > ${protobuf_temp} \
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
ARG rust_version=nightly-2020-10-19
RUN rustup toolchain install ${rust_version} \
  && rustup default ${rust_version}

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install musl target for Rust (for statically linked binaries).
RUN rustup target add aarch64-unknown-linux-musl

# Install rustfmt and clippy.
RUN rustup component add \
  clippy \
  rust-src \
  rustfmt

# No binary available on Github, have to use cargo install.
ARG deadlinks_version=0.5.0
RUN cargo install --locked --version=${deadlinks_version} cargo-deadlinks

# Where to install rust tooling
ARG install_dir=${rustup_dir}/bin

# Install grcov.
# https://github.com/mozilla/grcov
ARG grcov_version=0.5.15
RUN cargo install --version=${grcov_version} grcov

# Install cargo-crev.
# https://github.com/crev-dev/cargo-crev
# --target aarch64-unknown-linux-musl
ARG crev_version=0.18.0
RUN cargo install --locked --version=${crev_version} cargo-crev

# Install cargo-deny
# https://github.com/EmbarkStudios/cargo-deny
# --target aarch64-unknown-linux-musl
ARG deny_version=0.8.9
RUN cargo install --locked --version=${deny_version} cargo-deny

# Install cargo-udeps
# https://github.com/est31/cargo-udeps
ARG udeps_version=0.1.15
RUN cargo install --locked --version=${udeps_version} cargo-udeps

# Unset $CARGO_HOME so that the new user will use the default value for it, which will point it to
# its own home folder.
ENV CARGO_HOME ""

# Install sccache
# https://github.com/mozilla/sccache
ARG sccache_version=v0.2.15
ARG sccache_dir=/usr/local/sccache
ARG sccache_location=https://github.com/mozilla/sccache/releases/download/${sccache_version}/sccache-${sccache_version}-aarch64-unknown-linux-musl.tar.gz
ENV PATH "${sccache_dir}:${PATH}"
RUN mkdir --parents ${sccache_dir} \
  && curl --location ${sccache_location} | tar --extract --gzip --directory=${sccache_dir} --strip-components=1 \
  && chmod +x ${sccache_dir}/sccache

ENV SCCACHE_GCS_BUCKET sccache-1
ENV SCCACHE_GCS_KEY_PATH /workspaces/oak/.oak_remote_cache_key.json
ENV SCCACHE_GCS_RW_MODE READ_WRITE
ENV RUSTC_WRAPPER sccache
# Disable cargo incremental compilation, as it conflicts with sccache: https://github.com/mozilla/sccache#rust
ENV CARGO_INCREMENTAL false

# We use the `docker` user in order to maintain library paths on different
# machines and to make Wasm modules reproducible.
ARG USERNAME=docker

# Placeholder args that are expected to be passed in at image build time.
# See https://code.visualstudio.com/docs/remote/containers-advanced#_creating-a-nonroot-user
ARG USER_UID=1000
ARG USER_GID=${USER_UID}

# Create the specified user and group.
#
# Ignore errors if the user or group already exist (it should only happen if the image is being
# built as root, which happens on GCB).
RUN (groupadd --gid=${USER_GID} ${USERNAME} || true) \
  && (useradd --shell=/bin/bash --uid=${USER_UID} --gid=${USER_GID} --create-home ${USERNAME} || true)

# Set the default user as the newly created one, so that any operations performed from within the
# Docker container will appear as if performed by the outside user, instead of root.
USER ${USER_UID}
