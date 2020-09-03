# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/debian/snapshot/tags
ARG debian_snapshot=latest
# Use a fixed version of Bazel.
ARG bazel_version=3.0.0

# Build up the static musl toolchain using cross-build
FROM debian:${debian_snapshot} AS musl-build
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
FROM debian:${debian_snapshot} AS bazel-bootstrap
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
FROM bazel-bootstrap AS bazel-build
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  git 
WORKDIR /bazel/bazel-build
ARG bazel_version
RUN git clone -b ${bazel_version}  https://github.com/bazelbuild/bazel
WORKDIR /bazel/bazel-build/bazel 
COPY --from=bazel-bootstrap /bazel/bazel-dist/output/bazel ./bazel-bootstrap
RUN SOURCE_DATE_EPOCH=$(git log -1 --format=%ct) ./bazel-bootstrap build //src:bazel-dev --compilation_mode=opt

# Main Oak Build - We do not re-use the Bazel intermediates here
FROM debian:${debian_snapshot}

# Set the SHELL option -o pipefail before RUN with a pipe in.
# See https://github.com/hadolint/hadolint/wiki/DL4006
SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Uncomment the RUN below if the default snapshot package manager is slow.
# Please not that this might cause issues and affects reproducible builds,
# so only use for development.
# RUN echo \
#  deb http://ukdebian.mirror.anlx.net/debian buster main non-free contrib\
# > /etc/apt/sources.list

# Getting curl and certificates dependecies.
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  apt-transport-https \
  build-essential \
  ca-certificates \
  clang-tidy \
  curl \
  git \
  gnupg2 \
  gnupg-agent \
  libfl2 \
  libncurses5 \
  libssl-dev \
  musl-tools \
  npm \
  pkg-config \
  procps \
  protobuf-compiler \
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
COPY --from=bazel-build /bazel/bazel-build/bazel /usr/bin/bazel

# [aarch64] Pull in the musl compiler
COPY --from=musl-build /musl/musl-cross-make/output /usr

# Install the necessary binaries and SDKs, ordering them from the less frequently changed to the
# more frequently changed.
# See https://docs.docker.com/develop/develop-images/dockerfile_best-practices/#leverage-build-cache.

# [aarch64] Binaryen has components that require building from source as the
# packaging is amd64 specific.
# It is disabled for now - A multi-stage approach as per Bazel would seem semsible. 
# Install Emscripten.
#ARG emscripten_version=1.39.20
#ARG emscripten_node_version=12.9.1_64bit
#ARG emscripten_sha256=925dd5ca7dd783d0b367386e81847eaf680d54ae86017c4b5846dea951e17dc9

#ARG emscripten_dir=/usr/local/emsdk
#ARG emscripten_temp=/tmp/emscripten.zip
#RUN mkdir --parents ${emscripten_dir} \
#  && curl --location https://github.com/emscripten-core/emsdk/archive/${emscripten_version}.tar.gz > ${emscripten_temp} \
#  && sha256sum --binary ${emscripten_temp} && echo "${emscripten_sha256} *${emscripten_temp}" | sha256sum --check \
#  && tar --extract --gzip --file=${emscripten_temp} --directory=${emscripten_dir} --strip-components=1 \
#  && rm ${emscripten_temp} \
#  && ${emscripten_dir}/emsdk install ${emscripten_version} \
#  && ${emscripten_dir}/emsdk activate --embedded ${emscripten_version}
#ENV EMSDK "${emscripten_dir}"
#ENV EM_CONFIG "${emscripten_dir}/.emscripten"
#ENV EM_CACHE "${emscripten_dir}/.emscripten_cache"
#ENV PATH "${emscripten_dir}:${emscripten_dir}/node/${emscripten_node_version}/bin:${PATH}"
# We need to allow a non-root Docker container to write into the directory
#RUN chmod --recursive go+wx "${emscripten_dir}"
# Emscripten brings Node with it, we need to allow non-root access to temp folders
#RUN mkdir "/.npm" && chmod a+rwx "/.npm"

# Install Go.
ARG golang_version=1.14.6
# [amd64] ARG golang_sha256=aed845e4185a0b2a3c3d5e1d0a35491702c55889192bb9c30e67a3de6849c067
ARG golang_sha256=291bccfd7d7f1915599bbcc90e49d9fccfcb0004b7c62a2f5cdf0f96a09d6a3e
ARG golang_temp=/tmp/golang.tar.gz
ARG TARGETARCH
ENV GOROOT /usr/local/go
ENV GOPATH ${HOME}/go
ENV PATH "${GOROOT}/bin:${PATH}"
ENV PATH "${GOPATH}/bin:${PATH}"
RUN echo  "Getting go for Platform: $TARGETPLATFORM, OS: $TARGETOS, Arch: $TARGETARCH Variant: $TARGETVARIANT"
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
ARG prettier_version=1.19.1
ARG prettier_plugin_toml_version=0.3.1
ARG markdownlint_version=0.22.0
RUN npm install --global \
  prettier@${prettier_version} \
  prettier-plugin-toml@${prettier_plugin_toml_version} \
  markdownlint-cli@${markdownlint_version} \
  && prettier --version \
  && markdownlint --version


# This will require a from source approach as 
# stack have removed arm64 support due to CI limitations
# May require some integration with Haskell Community.
#
# Install hadolint.
# https://github.com/hadolint/hadolint
#ARG hadolint_version=1.17.5
#ARG hadolint_sha256=20dd38bc0602040f19268adc14c3d1aae11af27b463af43f3122076baf827a35
#ARG hadolint_dir=/usr/local/hadolint/bin
#ARG hadolint_bin=${hadolint_dir}/hadolint
#ENV PATH "${hadolint_dir}:${PATH}"
#RUN mkdir --parents ${hadolint_dir} \
#  && curl --location https://github.com/hadolint/hadolint/releases/download/v${hadolint_version}/hadolint-Linux-x86_64 > ${hadolint_bin} \
#  && sha256sum --binary ${hadolint_bin} && echo "${hadolint_sha256} *${hadolint_bin}" | sha256sum --check \
#  && chmod +x ${hadolint_bin} \
#  && hadolint --version

# Install buildifier.
# https://github.com/bazelbuild/buildtools/tree/master/buildifier
# ARG bazel_tools_version=2.2.1
# ARG buildifier_sha256=731a6a9bf8fca8a00a165cd5b3fbac9907a7cf422ec9c2f206b0a76c0a7e3d62
# ARG buildifier_dir=/usr/local/buildifier/bin
#ARG buildifier_bin=${buildifier_dir}/buildifier
#ENV PATH "${buildifier_dir}:${PATH}"
#RUN mkdir --parents ${buildifier_dir} \
#  && curl --location https://github.com/bazelbuild/buildtools/releases/download/${bazel_tools_version}/buildifier > ${buildifier_bin} \
#  && sha256sum --binary ${buildifier_bin} && echo "${buildifier_sha256} *${buildifier_bin}" | sha256sum --check \
#  && chmod +x ${buildifier_bin} \
#  && buildifier --version

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
RUN rustup target add aarch64-unknown-linux-musl

# Install rustfmt and clippy.
RUN rustup component add \
  clippy \
  rust-src \
  rustfmt

# No binary available on Github, have to use cargo install.
RUN cargo install cargo-deadlinks

# Where to install rust tooling
ARG install_dir=${rustup_dir}/bin

# Install grcov.
# https://github.com/mozilla/grcov
ARG grcov_version=v0.5.15
ARG grcov_location=https://github.com/mozilla/grcov/releases/download/${grcov_version}/grcov-linux-x86_64.tar.bz2
RUN curl --location ${grcov_location} | tar --extract --bzip2 --directory=${install_dir}
RUN chmod +x ${install_dir}/grcov

# Install cargo-crev.
# https://github.com/crev-dev/cargo-crev
ARG crev_version=v0.16.1
ARG crev_location=https://github.com/crev-dev/cargo-crev/releases/download/${crev_version}/cargo-crev-${crev_version}-x86_64-unknown-linux-musl.tar.gz
RUN curl --location ${crev_location} | tar --extract --gzip --directory=${install_dir} --strip-components=1
RUN chmod +x ${install_dir}/cargo-crev

# Install cargo-deny
# https://github.com/EmbarkStudios/cargo-deny
ARG deny_version=0.7.0
ARG deny_location=https://github.com/EmbarkStudios/cargo-deny/releases/download/${deny_version}/cargo-deny-${deny_version}-x86_64-unknown-linux-musl.tar.gz
RUN curl --location ${deny_location} | tar --extract --gzip --directory=${install_dir} --strip-components=1
RUN chmod +x ${install_dir}/cargo-deny
