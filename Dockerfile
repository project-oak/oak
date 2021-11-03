# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/debian/snapshot/tags
ARG debian_snapshot=buster-20210927
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
  curl \
  git \
  gnupg2 \
  gnupg-agent \
  libfl2 \
  libncurses5 \
  libssl-dev \
  musl-tools \
  openjdk-11-jdk \
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
ARG bazel_version=4.2.0
ARG bazel_sha256=89b14fa0d9ce5637f4e0b66df56a531e1e3c50d88614311334d192531cf1e0fa
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
# Pick compatible Node version by grepping "node" in the emscripten.zip
# Node is needed to expose npm needed for installing Prettier.
ARG emscripten_node_version_directory=12.9.1_64bit
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
ENV PATH "${emscripten_dir}:${emscripten_dir}/node/${emscripten_node_version_directory}/bin:${PATH}"
# We need to allow a non-root Docker container to write into the directory
RUN chmod --recursive go+wx "${emscripten_dir}"
# Emscripten brings Node with it, we need to allow non-root access to temp and
# config folders
RUN mkdir -p "/.npm" && chmod a+rwx "/.npm" & mkdir -p "/.config" && chmod a+rwx "/.config"

# Install Go.
ARG golang_version=1.17.1
ARG golang_sha256=dab7d9c34361dc21ec237d584590d72500652e7c909bf082758fb63064fca0ef
ARG golang_temp=/tmp/golang.tar.gz
ENV GOROOT /usr/local/go
ENV GOPATH ${HOME}/go
ENV PATH "${GOROOT}/bin:${PATH}"
ENV PATH "${GOPATH}/bin:${PATH}"
# Enable Go module behaviour even in the presence of GOPATH; this way we can specify precise
# versions via `go install`.
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
RUN go get github.com/raviqqe/liche@3ac05a3 \
  && liche --version

# Install prettier and markdownlint (via Node.js).
# This will use the Node version installed by emscripten.
# https://prettier.io/
# https://github.com/igorshubovych/markdownlint-cli
ARG prettier_version=2.4.1
ARG prettier_plugin_toml_version=0.3.1
ARG markdownlint_version=0.24.0
RUN npm install --global \
  prettier@${prettier_version} \
  prettier-plugin-toml@${prettier_plugin_toml_version} \
  markdownlint-cli@${markdownlint_version} \
  && prettier --version \
  && markdownlint --version

# Install hadolint.
# https://github.com/hadolint/hadolint
ARG hadolint_version=2.7.0
ARG hadolint_sha256=cdd5ca6f07f72053e8f2d18a9390a7b7fc6e819b6a251835971411f300dab8e6
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
ARG bazel_tools_version=4.2.2
ARG buildifier_sha256=3f0e450cd852dbfd89aa2761d85f9fbeb6f0faccfc5d4fbe48952cfe0712922a
ARG buildifier_dir=/usr/local/buildifier/bin
ARG buildifier_bin=${buildifier_dir}/buildifier
ENV PATH "${buildifier_dir}:${PATH}"
RUN mkdir --parents ${buildifier_dir} \
  && curl --location https://github.com/bazelbuild/buildtools/releases/download/${bazel_tools_version}/buildifier > ${buildifier_bin} \
  && sha256sum --binary ${buildifier_bin} && echo "${buildifier_sha256} *${buildifier_bin}" | sha256sum --check \
  && chmod +x ${buildifier_bin} \
  && buildifier --version

# Install Protobuf compiler.
ARG protobuf_version=3.18.0
ARG protobuf_sha256=8b6b0c82f730212801d9cce4653abb1a1f4204555a92e8e2b5f625d61e66f1b4
ARG protobuf_dir=/usr/local/protobuf
ARG protobuf_temp=/tmp/protobuf.zip
ENV PATH "${protobuf_dir}/bin:${PATH}"
RUN curl --location https://github.com/protocolbuffers/protobuf/releases/download/v${protobuf_version}/protoc-${protobuf_version}-linux-x86_64.zip > ${protobuf_temp} \
  && sha256sum --binary ${protobuf_temp} && echo "${protobuf_sha256} *${protobuf_temp}" | sha256sum --check \
  && unzip ${protobuf_temp} -d ${protobuf_dir} \
  && rm ${protobuf_temp} \
  && chmod --recursive a+rwx ${protobuf_dir} \
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
ARG rust_version=nightly-2021-08-17
# when updating to rust_version=nightly-2021-11-02
# change cargo-fuzz to the following to avoid a recent failure
# cf. https://github.com/rust-fuzz/cargo-fuzz/pull/277
# RUN cargo install --git https://github.com/rust-fuzz/cargo-fuzz/ --rev 8c964bf183c93cd49ad655eb2f3faecf543d0012
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
# https://github.com/deadlinks/cargo-deadlinks
ARG deadlinks_version=0.8.0
RUN cargo install --version=${deadlinks_version} cargo-deadlinks

# Install cargo-fuzz.
# To allow local testing of the fuzzing functionality.
# https://github.com/rust-fuzz/cargo-fuzz
ARG cargo_fuzz_version=0.10.1
RUN cargo install --version=${cargo_fuzz_version} cargo-fuzz

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
ARG crev_version=v0.18.0
ARG crev_location=https://github.com/crev-dev/cargo-crev/releases/download/${crev_version}/cargo-crev-${crev_version}-x86_64-unknown-linux-musl.tar.gz
RUN curl --location ${crev_location} | tar --extract --gzip --directory=${install_dir} --strip-components=1
RUN chmod +x ${install_dir}/cargo-crev

# Install cargo-deny
# https://github.com/EmbarkStudios/cargo-deny
ARG deny_version=0.9.1
ARG deny_location=https://github.com/EmbarkStudios/cargo-deny/releases/download/${deny_version}/cargo-deny-${deny_version}-x86_64-unknown-linux-musl.tar.gz
RUN curl --location ${deny_location} | tar --extract --gzip --directory=${install_dir} --strip-components=1
RUN chmod +x ${install_dir}/cargo-deny

# Install cargo-udeps
# https://github.com/est31/cargo-udeps
ARG udeps_version=v0.1.23
ARG udeps_dir=cargo-udeps-${udeps_version}-x86_64-unknown-linux-gnu
ARG udeps_location=https://github.com/est31/cargo-udeps/releases/download/${udeps_version}/cargo-udeps-${udeps_version}-x86_64-unknown-linux-gnu.tar.gz
RUN curl --location ${udeps_location} | tar --extract --gzip --directory=${install_dir} --strip-components=2 ./${udeps_dir}/cargo-udeps
RUN chmod +x ${install_dir}/cargo-udeps

# Install rust-analyzer
# https://github.com/rust-analyzer/rust-analyzer
ARG rust_analyzer_version=2021-08-16
ARG rust_analyzer_location=https://github.com/rust-analyzer/rust-analyzer/releases/download/${rust_analyzer_version}/rust-analyzer-x86_64-unknown-linux-gnu.gz
RUN curl --location ${rust_analyzer_location} | gzip --decompress "$@" > ${install_dir}/rust-analyzer
RUN chmod +x ${install_dir}/rust-analyzer

# Unset $CARGO_HOME so that the new user will use the default value for it, which will point it to
# its own home folder.
ENV CARGO_HOME ""

# Build a statically-linked version of OpenSSL with musl
ENV OPENSSL_DIR /musl
RUN mkdir ${OPENSSL_DIR}

RUN ln -s /usr/include/x86_64-linux-gnu/asm /usr/include/x86_64-linux-musl/asm
RUN ln -s /usr/include/asm-generic /usr/include/x86_64-linux-musl/asm-generic
RUN ln -s /usr/include/linux /usr/include/x86_64-linux-musl/linux

ARG openssl_dir=/usr/local/openssl
RUN mkdir --parents ${openssl_dir}
RUN curl --location https://github.com/openssl/openssl/archive/OpenSSL_1_1_1f.tar.gz | tar --extract --gzip --directory=${openssl_dir}/
WORKDIR ${openssl_dir}/openssl-OpenSSL_1_1_1f
RUN CC="musl-gcc -fPIE -pie" ./Configure no-shared no-async --prefix=/musl --openssldir="${OPENSSL_DIR}/ssl" linux-x86_64
RUN make depend && make -j"$(nproc)"&& make install_sw install_ssldirs

# Allow the build to find statically built OpenSSL.
ENV PKG_CONFIG_ALLOW_CROSS 1
ENV OPENSSL_STATIC 1

# Install sccache
# https://github.com/mozilla/sccache
ARG sccache_version=v0.2.15
ARG sccache_dir=/usr/local/sccache
ARG sccache_location=https://github.com/mozilla/sccache/releases/download/${sccache_version}/sccache-${sccache_version}-x86_64-unknown-linux-musl.tar.gz
ENV PATH "${sccache_dir}:${PATH}"
RUN mkdir --parents ${sccache_dir} \
  && curl --location ${sccache_location} | tar --extract --gzip --directory=${sccache_dir} --strip-components=1 \
  && chmod +x ${sccache_dir}/sccache

ENV SCCACHE_GCS_BUCKET sccache-1
ENV SCCACHE_GCS_KEY_PATH /workspace/.oak_remote_cache_key.json
ENV SCCACHE_GCS_RW_MODE READ_WRITE

# TODO(#2014): Re-enable sccache once runner runs backend binaries directly rather than using `cargo run`.
# ENV RUSTC_WRAPPER sccache

# Disable cargo incremental compilation, as it conflicts with sccache: https://github.com/mozilla/sccache#rust
ENV CARGO_INCREMENTAL false

# We use the `docker` user in order to maintain library paths on different
# machines and to make Wasm modules reproducible.
#
# We do not set this as the default user in the Docker image, because we expect its uid not to match
# uid of the host, therefore we need to first fix the uid before actually using the user. This is
# done by /scripts/fix_docker_user_and_run .
RUN useradd --shell=/bin/bash --create-home --user-group docker
