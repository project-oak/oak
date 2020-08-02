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

# Getting curl and certificates dependecies.
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes \
  apt-transport-https \
  build-essential \
  ca-certificates \
  clang-tidy \
  # `cmake` is needed for `minisign`.
  cmake \
  curl \
  git \
  gnupg2 \
  gnupg-agent \
  libfl2 \
  libncurses5 \
  # `libsodium-dev` is needed for `minisign`.
  libsodium-dev \
  libssl-dev \
  musl-tools \
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
RUN echo "deb [arch=amd64] https://download.docker.com/linux/debian buster stable"  > /etc/apt/sources.list.d/backports.list \
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
ARG emscripten_version=1.39.17
ARG emscripten_node_version=12.9.1_64bit
ARG emscripten_sha256=925dd5ca7dd783d0b367386e81847eaf680d54ae86017c4b5846dea951e17dc9

ARG emscripten_dir=/usr/local/emsdk
ARG emscripten_temp=/tmp/emscripten.zip
RUN mkdir --parents ${emscripten_dir} \
  && curl --location https://github.com/emscripten-core/emsdk/archive/${emscripten_version}.tar.gz > ${emscripten_temp} \
  && sha256sum --binary ${emscripten_temp} && echo "${emscripten_sha256} *${emscripten_temp}" | sha256sum --check \
  && tar --extract --gzip --file=${emscripten_temp} --directory=${emscripten_dir} --strip-components=1 \
  && rm ${emscripten_temp} \
  && ${emscripten_dir}/emsdk install ${emscripten_version} \
  && ${emscripten_dir}/emsdk activate --embedded ${emscripten_version}
ENV EMSDK "${emscripten_dir}"
ENV EM_CONFIG "${emscripten_dir}/.emscripten"
ENV EM_CACHE "${emscripten_dir}/.emscripten_cache"
ENV PATH "${emscripten_dir}:${emscripten_dir}/node/${emscripten_node_version}/bin:${PATH}"
# We need to allow a non-root Docker container to write into the directory
RUN chmod --recursive go+wx "${emscripten_dir}"
# Emscripten brings Node with it, we need to allow non-root access to temp and
# config folders
RUN mkdir -p "/.npm" && chmod a+rwx "/.npm" & mkdir -p "/.config" && chmod a+rwx "/.config"

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

# Install hadolint.
# https://github.com/hadolint/hadolint
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
# https://github.com/bazelbuild/buildtools/tree/master/buildifier
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
ARG rust_version=nightly-2020-06-10
RUN rustup toolchain install ${rust_version} \
  && rustup default ${rust_version}

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install musl target for Rust (for statically linked binaries).
RUN rustup target add x86_64-unknown-linux-musl

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

# Install minisign.
# https://github.com/jedisct1/minisign
ARG minisign_version=0.9
ARG minisign_sha256=220383976aacb642c1f2946ec574f6ff4cc2470f59352ed618185353f7762cc1
ARG minisign_dir=/usr/local/minisign
ARG minisign_temp=/tmp/minisign.tar.gz
RUN mkdir --parents ${minisign_dir}/build \
  && curl --location https://github.com/jedisct1/minisign/releases/download/${minisign_version}/minisign-${minisign_version}.tar.gz > ${minisign_temp} \
  && sha256sum --binary ${minisign_temp} && echo "${minisign_sha256} *${minisign_temp}" | sha256sum --check \
  && tar --extract --gzip --file=${minisign_temp} --directory=${minisign_dir} --strip-components=1 \
  && rm ${minisign_temp} \
  && cd ${minisign_dir}/build \
  && cmake .. \
  && make \
  && make install

# Unset $CARGO_HOME so that the new user will use the default value for it, which will point it to
# its own home folder.
ENV CARGO_HOME ""

# Placeholder args that are expected to be passed in at image build time.
# See https://code.visualstudio.com/docs/remote/containers-advanced#_creating-a-nonroot-user
ARG USERNAME=user-name-goes-here
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
