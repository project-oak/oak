# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/debian/snapshot/tags
ARG debian_snapshot=buster-20200327
FROM debian/snapshot:${debian_snapshot}

# Set the SHELL option -o pipefail before RUN with a pipe in.
# See https://github.com/hadolint/hadolint/wiki/DL4006
SHELL ["/bin/bash", "-o", "pipefail", "-c"]

RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  build-essential \
  clang-format \
  clang-tidy \
  curl \
  default-jdk-headless \
  git \
  libfl2 \
  libncurses5 \
  libssl-dev \
  musl-tools \
  pkg-config \
  procps \
  python-dev \
  python2.7-dev \
  python3-dev \
  python3-six \
  shellcheck \
  vim \
  xml2 \
  # `unzip` and `zlib1g-dev` are needed for Bazel.
  unzip \
  zlib1g-dev \
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/* \
  # Print version of various installed tools.
  && git --version \
  && clang-format -version \
  && shellcheck --version

# Use a later version of clang-format from buster-backports.
RUN echo 'deb http://deb.debian.org/debian buster-backports main' > /etc/apt/sources.list.d/backports.list \
  && apt-get --yes update \
  && apt-get install --no-install-recommends --yes clang-format-8 \
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/* \
  && ln --symbolic --force clang-format-8 /usr/bin/clang-format

# Use a fixed version of Bazel.
ARG bazel_version=3.0.0
ARG bazel_sha256=dfa79c10bbfa39cd778e1813a273fd3236beb495497baa046f26d393c58bdc35
ARG bazel_url=https://storage.googleapis.com/bazel-apt/pool/jdk1.8/b/bazel/bazel_${bazel_version}_amd64.deb
RUN curl --location "${bazel_url}" > bazel.deb \
  && sha256sum --binary bazel.deb && echo "${bazel_sha256} *bazel.deb" | sha256sum --check \
  && apt-get install --no-install-recommends --yes ./bazel.deb \
  && rm bazel.deb \
  && apt-get clean \
  && bazel version

# Install the necessary binaries and SDKs, ordering them from the less frequently changed to the
# more frequently changed.
# See https://docs.docker.com/develop/develop-images/dockerfile_best-practices/#leverage-build-cache.

# Install Emscripten.
ARG emscripten_version=1.39.6
ARG emscripten_commit=6bfbe2a7da68e650054af2d272d2b79307a6ad72
ARG emscripten_sha256=aa4c3b8f23fd26363f98207674bffcc138105c621c6c8bf12175f6aab1231357
ARG emscripten_dir=/usr/local/emsdk
ARG emscripten_temp=/tmp/emscripten.zip
RUN mkdir --parents ${emscripten_dir} \
  && curl --location https://github.com/emscripten-core/emsdk/archive/${emscripten_commit}.tar.gz > ${emscripten_temp} \
  && sha256sum --binary ${emscripten_temp} && echo "${emscripten_sha256} *${emscripten_temp}" | sha256sum --check \
  && tar --extract --gzip --file=${emscripten_temp} --directory=${emscripten_dir} --strip-components=1 \
  && rm ${emscripten_temp} \
  && ${emscripten_dir}/emsdk install ${emscripten_version} \
  && ${emscripten_dir}/emsdk activate --embedded ${emscripten_version}
ENV EMSDK "${emscripten_dir}"
ENV EM_CONFIG "${emscripten_dir}/.emscripten"
ENV EM_CACHE "${emscripten_dir}/.emscripten_cache"
# We need to allow a non-root Docker container to write into the `EM_CACHE` directory.
RUN chmod --recursive go+wx "${EM_CACHE}"

# Install Go.
ARG golang_version=1.14.4
ARG golang_sha256=aed845e4185a0b2a3c3d5e1d0a35491702c55889192bb9c30e67a3de6849c067
ARG golang_temp=/tmp/golang.tar.gz
ENV GOROOT /usr/local/go
ENV GOPATH ${HOME}/go
ENV PATH "${GOROOT}/bin:${PATH}"
ENV PATH "${GOPATH}/bin:${PATH}"
# Enable Go module behaviour even in the presence of GOPATH; this way we can specify precise
# versions via `go get`.
# See https://dev.to/maelvls/why-is-go111module-everywhere-and-everything-about-go-modules-24k
ENV GO111MODULE on
RUN mkdir --parents ${GOROOT} \
  && curl --location https://dl.google.com/go/go${golang_version}.linux-amd64.tar.gz > ${golang_temp} \
  && sha256sum --binary ${golang_temp} && echo "${golang_sha256} *${golang_temp}" | sha256sum --check \
  && tar --extract --gzip --file=${golang_temp} --directory=${GOROOT} --strip-components=1 \
  && rm ${golang_temp} \
  && go version

# Install embedmd (Markdown snippet embedder) (via Go).
RUN go get github.com/campoy/embedmd@97c13d6 \
  && embedmd -v

# Install liche (Markdown link checker) (via Go).
RUN go get github.com/raviqqe/liche@f57a5d1 \
  && liche --version

ARG hadolint_version=1.17.5
ARG hadolint_sha256=20dd38bc0602040f19268adc14c3d1aae11af27b463af43f3122076baf827a35
ARG hadolint_dir=/usr/local/hadolint/bin
ARG hadolint_bin=${hadolint_dir}/hadolint
ENV PATH "${hadolint_dir}:${PATH}"
RUN mkdir --parents ${hadolint_dir} \
  && curl --location https://github.com/hadolint/hadolint/releases/download/v${hadolint_version}/hadolint-Linux-x86_64 > ${hadolint_bin} \
  && sha256sum --binary ${hadolint_bin} && echo "${hadolint_sha256} *${hadolint_bin}" | sha256sum --check \
  && chmod +x ${hadolint_bin} \
  && hadolint --version

# Install buildifier.
ARG bazel_tools_version=2.2.1
ARG buildifier_sha256=731a6a9bf8fca8a00a165cd5b3fbac9907a7cf422ec9c2f206b0a76c0a7e3d62
ARG buildifier_dir=/usr/local/buildifier/bin
ARG buildifier_bin=${buildifier_dir}/buildifier
ENV PATH "${buildifier_dir}:${PATH}"
RUN mkdir --parents ${buildifier_dir} \
  && curl --location https://github.com/bazelbuild/buildtools/releases/download/${bazel_tools_version}/buildifier > ${buildifier_bin} \
  && sha256sum --binary ${buildifier_bin} && echo "${buildifier_sha256} *${buildifier_bin}" | sha256sum --check \
  && chmod +x ${buildifier_bin} \
  && buildifier --version

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
# Make sure to update WORKSPACE too, e.g. when updating nightly version
ARG rust_version=nightly-2020-04-17
RUN rustup toolchain install ${rust_version} \
  && rustup default ${rust_version}

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install musl target for Rust (for statically linked binaries).
RUN rustup target add x86_64-unknown-linux-musl

# Install rustfmt, clippy, and the Rust Language Server.
RUN rustup component add \
  clippy \
  rls \
  rust-analysis \
  rust-src \
  rustfmt

RUN cargo install cargo-deadlinks
RUN cargo install cargo-deny

# Install Node.js.
RUN curl --location https://deb.nodesource.com/setup_12.x | bash - \
  && apt-get install --no-install-recommends --yes nodejs \
  && node --version \
  && npm --version

# Install yarn, a Node.js package manager.
ENV YARN_VERSION 1.22.4
RUN curl -fsSLO --compressed "https://yarnpkg.com/downloads/$YARN_VERSION/yarn-v$YARN_VERSION.tar.gz" \
  && mkdir -p /opt \
  && tar -xzf yarn-v$YARN_VERSION.tar.gz -C /opt/ \
  && ln -s /opt/yarn-v$YARN_VERSION/bin/yarn /usr/local/bin/yarn \
  && ln -s /opt/yarn-v$YARN_VERSION/bin/yarnpkg /usr/local/bin/yarnpkg \
  && rm yarn-v$YARN_VERSION.tar.gz \
  && yarn --version

# Install prettier and markdownlint (via yarn / Node.js).
# https://prettier.io/
# https://github.com/igorshubovych/markdownlint-cli
ARG prettier_version=1.19.1
ARG prettier_plugin_toml_version=0.3.1
ARG markdownlint_version=0.22.0
RUN yarn global add \
  prettier@${prettier_version} \
  prettier-plugin-toml@${prettier_plugin_toml_version} \
  markdownlint-cli@${markdownlint_version} \
  && prettier --version \
  && markdownlint --version
