# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/debian/snapshot/tags?name=bullseye
ARG debian_snapshot=sha256:d647c95797c43e8ef0e0667c4b4acba752ae70385dcf648877903f15c8977da4
FROM debian/snapshot@${debian_snapshot}

# Set the SHELL option -o pipefail before RUN with a pipe in.
# See https://github.com/hadolint/hadolint/wiki/DL4006
SHELL ["/bin/bash", "-o", "pipefail", "-c"]

# Uncomment the RUN below if the default snapshot package manager is slow.
# Please not that this might cause issues and affects reproducible builds,
# so only use for development.
# RUN echo \
#  deb [arch=amd64] http://ukdebian.mirror.anlx.net/debian buster main non-free contrib\
# > /etc/apt/sources.list

# First install the minimal set of utils that will be used to setup the rest of the packages to install.
RUN apt-get --yes update && apt-get install --no-install-recommends --yes curl gnupg2 gnupg-agent ca-certificates

# Install LLDB for debugging support.
ARG llvm_version=14
RUN curl --fail --silent --show-error --location https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add -
RUN echo "deb http://apt.llvm.org/bullseye/ llvm-toolchain-bullseye-$llvm_version main" >> /etc/apt/sources.list.d/llvm.list

# Install docker CLI.
RUN curl --fail --silent --show-error --location https://download.docker.com/linux/debian/gpg | apt-key add -
RUN echo "deb [arch=amd64] https://download.docker.com/linux/debian bullseye stable"  > /etc/apt/sources.list.d/backports.list

# Install NodeJS
# https://github.com/nodesource/distributions/blob/master/README.md#manual-installation
RUN curl --fail --silent --show-error --location https://deb.nodesource.com/gpgkey/nodesource.gpg.key | apt-key add -
RUN echo "deb https://deb.nodesource.com/node_18.x bullseye main" > /etc/apt/sources.list.d/nodesource.list

# Getting curl and certificates dependecies.
# We're rate-limiting HTTP requests to 500 kB/s as otherwise we may get timeout errors
# when downloading from snapshot.debian.org.
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes --option Acquire::http::Dl-Limit=500 \
  apt-transport-https \
  build-essential \
  ca-certificates \
  # `chromium` is required to run our tests with wasm-pack.
  chromium \
  chromium-driver \
  clang-format \
  clang-tidy \
  # `cmake` is needed for flatbuffer.
  cmake \
  # `cpio` is needed for creating initial RAM disks.
  cpio \
  curl \
  docker-ce-cli \
  git \
  gnupg2 \
  gnupg-agent \
  libcap-dev \
  libfl2 \
  libncurses5 \
  libssl-dev \
  lldb-${llvm_version} \
  musl-tools \
  nodejs \
  openjdk-11-jdk \
  pkg-config \
  procps \
  python3 \
  python3-six \
  python3-distutils \
  qemu-system-x86 \
  shellcheck \
  software-properties-common \
  texinfo \
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

# Install Ent CLI. We mostly then just use it in order to simplify the logic around fetching
# artifacts by URL and ensuring that their digest is correct, in order to ensure reproducibility.
ARG ent_server_url=https://ent-server-62sa4xcfia-ew.a.run.app
ARG ent_digest=sha256:b2e999bda4c90fc58c924e19787f5f7037f9d48fd83e7deebd06e3e1d5b31e8d
RUN curl --location ${ent_server_url}/raw/${ent_digest} > /usr/local/bin/ent \
  && chmod +x /usr/local/bin/ent \
  && ent

# Use a fixed version of Bazel.
ARG bazel_version=5.3.1
ARG bazel_digest=sha256:1e939b50d90f68d30fa4f3c12dfdf31429b83ddd8076c622429854f64253c23d
ARG bazel_url=https://storage.googleapis.com/bazel-apt/pool/jdk1.8/b/bazel/bazel_${bazel_version}_amd64.deb
RUN ent get ${bazel_digest} --url=${bazel_url} > bazel.deb \
  && apt-get install --no-install-recommends --yes ./bazel.deb \
  && rm bazel.deb \
  && apt-get clean \
  && bazel version

# Install the necessary binaries and SDKs, ordering them from the less frequently changed to the
# more frequently changed.
# See https://docs.docker.com/develop/develop-images/dockerfile_best-practices/#leverage-build-cache.

# Install Go.
# https://go.dev/dl/
ARG golang_version=1.19.2
ARG golang_digest=sha256:5e8c5a74fe6470dd7e055a461acda8bb4050ead8c2df70f227e3ff7d8eb7eeb6
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
  && ent get ${golang_digest} --url=https://dl.google.com/go/go${golang_version}.linux-amd64.tar.gz > ${golang_temp} \
  && tar --extract --gzip --file=${golang_temp} --directory=${GOROOT} --strip-components=1 \
  && rm ${golang_temp} \
  && go version

# Install embedmd (Markdown snippet embedder) (via Go).
# https://github.com/campoy/embedmd
RUN go install github.com/campoy/embedmd@97c13d6 \
  && embedmd -v

# Install liche (Markdown link checker) (via Go).
# https://github.com/raviqqe/liche
RUN go install github.com/raviqqe/liche@f9ba5f2 \
  && liche --version

# Install prettier and markdownlint (via Node.js).
# This will use the Node version installed by emscripten.
# https://prettier.io/
# https://github.com/prettier/prettier
# https://github.com/igorshubovych/markdownlint-cli
ARG prettier_version=2.7.1
ARG prettier_plugin_toml_version=0.3.1
ARG markdownlint_version=0.32.2
RUN npm install --global \
  prettier@${prettier_version} \
  prettier-plugin-toml@${prettier_plugin_toml_version} \
  markdownlint-cli@${markdownlint_version} \
  && prettier --version \
  && markdownlint --version

# Install hadolint.
# https://github.com/hadolint/hadolint
ARG hadolint_version=2.10.0
ARG hadolint_digest=sha256:8ee6ff537341681f9e91bae2d5da451b15c575691e33980893732d866d3cefc4
ARG hadolint_dir=/usr/local/hadolint/bin
ARG hadolint_bin=${hadolint_dir}/hadolint
ENV PATH "${hadolint_dir}:${PATH}"
RUN mkdir --parents ${hadolint_dir} \
  && ent get ${hadolint_digest} --url=https://github.com/hadolint/hadolint/releases/download/v${hadolint_version}/hadolint-Linux-x86_64 > ${hadolint_bin} \
  && chmod +x ${hadolint_bin} \
  && hadolint --version

# Install buildifier.
# https://github.com/bazelbuild/buildtools/tree/master/buildifier
ARG bazel_tools_version=5.1.0
ARG buildifier_digest=sha256:52bf6b102cb4f88464e197caac06d69793fa2b05f5ad50a7e7bf6fbd656648a3
ARG buildifier_dir=/usr/local/buildifier/bin
ARG buildifier_bin=${buildifier_dir}/buildifier
ENV PATH "${buildifier_dir}:${PATH}"
RUN mkdir --parents ${buildifier_dir} \
  && ent get ${buildifier_digest} --url=https://github.com/bazelbuild/buildtools/releases/download/${bazel_tools_version}/buildifier-linux-amd64 > ${buildifier_bin} \
  && chmod +x ${buildifier_bin} \
  && buildifier --version

# Install Protobuf compiler.
# https://github.com/protocolbuffers/protobuf
ARG protobuf_version=3.20.3
ARG protobuf_digest=sha256:44a6b498e996b845edef83864734c0e52f42197e85c9d567af55f4e3ff09d755
ARG protobuf_dir=/usr/local/protobuf
ARG protobuf_temp=/tmp/protobuf.zip
ENV PATH "${protobuf_dir}/bin:${PATH}"
RUN ent get ${protobuf_digest} --url=https://github.com/protocolbuffers/protobuf/releases/download/v${protobuf_version}/protoc-${protobuf_version}-linux-x86_64.zip > ${protobuf_temp} \
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
ARG rust_version=nightly-2023-02-13
RUN rustup toolchain install ${rust_version} \
  && rustup default ${rust_version}

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install musl target for Rust (for statically linked binaries).
RUN rustup target add x86_64-unknown-linux-musl

# Install freestanding target for Rust (for enclave binaries).
RUN rustup target add x86_64-unknown-none

# Install various components we need.
RUN rustup component add \
  clippy \
  llvm-tools-preview \
  rust-src \
  rustfmt

# No binary available on Github, have to use cargo install.
# https://github.com/deadlinks/cargo-deadlinks
ARG deadlinks_version=0.8.1
RUN cargo install --version=${deadlinks_version} cargo-deadlinks

# Install cargo-fuzz.
# To allow local testing of the fuzzing functionality.
# https://github.com/rust-fuzz/cargo-fuzz
# change cargo-fuzz to the following to avoid a recent failure
# cf. https://github.com/rust-fuzz/cargo-fuzz/pull/277
RUN cargo install --git https://github.com/rust-fuzz/cargo-fuzz/ --rev 8c964bf183c93cd49ad655eb2f3faecf543d0012

# Install cargo-binutils.
ARG binutils_version=0.3.6
RUN cargo install --version=${binutils_version} cargo-binutils

# Where to install rust tooling
ARG install_dir=${rustup_dir}/bin

# Install grcov.
# https://github.com/mozilla/grcov
ARG grcov_version=v0.8.13
ARG grcov_location=https://github.com/mozilla/grcov/releases/download/${grcov_version}/grcov-x86_64-unknown-linux-musl.tar.bz2
RUN curl --location ${grcov_location} | tar --extract --bzip2 --directory=${install_dir}
RUN chmod +x ${install_dir}/grcov

# Install cargo-deny
# https://github.com/EmbarkStudios/cargo-deny
ARG deny_version=0.13.7
ARG deny_location=https://github.com/EmbarkStudios/cargo-deny/releases/download/${deny_version}/cargo-deny-${deny_version}-x86_64-unknown-linux-musl.tar.gz
RUN curl --location ${deny_location} | tar --extract --gzip --directory=${install_dir} --strip-components=1
RUN chmod +x ${install_dir}/cargo-deny

# Install cargo-udeps
# https://github.com/est31/cargo-udeps
ARG udeps_version=0.1.35
ARG udeps_dir=cargo-udeps-v${udeps_version}-x86_64-unknown-linux-gnu
ARG udeps_location=https://github.com/est31/cargo-udeps/releases/download/v${udeps_version}/cargo-udeps-v${udeps_version}-x86_64-unknown-linux-gnu.tar.gz
RUN curl --location ${udeps_location} | tar --extract --gzip --directory=${install_dir} --strip-components=2 ./${udeps_dir}/cargo-udeps
RUN chmod +x ${install_dir}/cargo-udeps

# Install rust-analyzer
# https://github.com/rust-analyzer/rust-analyzer
ARG rust_analyzer_version=2023-02-13
ARG rust_analyzer_location=https://github.com/rust-analyzer/rust-analyzer/releases/download/${rust_analyzer_version}/rust-analyzer-x86_64-unknown-linux-gnu.gz
RUN curl --location ${rust_analyzer_location} | gzip --decompress "$@" > ${install_dir}/rust-analyzer
RUN chmod +x ${install_dir}/rust-analyzer

# Unset $CARGO_HOME so that the new user will use the default value for it, which will point it to
# its own home folder.
ENV CARGO_HOME ""

# Install sccache
# https://github.com/mozilla/sccache
ARG sccache_version=0.3.3
ARG sccache_dir=/usr/local/sccache
ARG sccache_location=https://github.com/mozilla/sccache/releases/download/v${sccache_version}/sccache-v${sccache_version}-x86_64-unknown-linux-musl.tar.gz
ENV PATH "${sccache_dir}:${PATH}"
RUN mkdir --parents ${sccache_dir} \
  && curl --location ${sccache_location} | tar --extract --gzip --directory=${sccache_dir} --strip-components=1 \
  && chmod +x ${sccache_dir}/sccache

# Install wasm-pack.
# https://github.com/rustwasm/wasm-pack
ARG wasm_pack_version=0.10.2
ARG wasm_pack_digest=sha256:ddf59a454fbee8712932803583d01756204c32fbfb13defa69f08c3e7afb6ac5
ARG wasm_pack_tmp=/tmp/wasm-pack
ARG wasm_pack_dir=/usr/local/wasm-pack/bin
ARG wasm_pack_bin=${wasm_pack_dir}/wasm-pack
ENV PATH "${wasm_pack_dir}:${PATH}"
RUN mkdir --parents ${wasm_pack_dir} \
  && ent get ${wasm_pack_digest} --url=https://github.com/rustwasm/wasm-pack/releases/download/v${wasm_pack_version}/wasm-pack-v${wasm_pack_version}-x86_64-unknown-linux-musl.tar.gz > ${wasm_pack_tmp} \
  && tar --extract --gzip --file=${wasm_pack_tmp} --directory=${wasm_pack_dir} --strip-components=1 \
  && rm ${wasm_pack_tmp} \
  && chmod +x ${wasm_pack_bin} \
  && wasm-pack --version

# By default, sccache uses `~/.cache/sccache` locally: https://github.com/mozilla/sccache#local.
ENV RUSTC_WRAPPER sccache

# Disable cargo incremental compilation, as it conflicts with sccache: https://github.com/mozilla/sccache#rust
ENV CARGO_INCREMENTAL false

# Install Android SDK.
# https://developer.android.com/studio/#downloads
# https://developer.android.com/studio/index.html#command-tools
ARG android_sdk_version=8512546
ENV ANDROID_HOME /opt/android-sdk
ENV android_temp /tmp/android-sdk
RUN mkdir --parents "{android_temp}" \
    && mkdir --parents "${ANDROID_HOME}/cmdline-tools/latest" \
    && curl --location "https://dl.google.com/android/repository/commandlinetools-linux-${android_sdk_version}_latest.zip" > android_sdk.zip \
    && unzip android_sdk.zip -d "${android_temp}" \
    && mv ${android_temp}/cmdline-tools/* "${ANDROID_HOME}/cmdline-tools/latest/" \
    && rm android_sdk.zip

# Install Android Platform Tools.
# https://developer.android.com/studio/releases/platform-tools
# https://developer.android.com/studio/releases/platforms
# https://developer.android.com/studio/releases/build-tools
ARG platform=30
ARG tools=30.0.0
RUN "${ANDROID_HOME}/cmdline-tools/latest/bin/sdkmanager" --update \
    && (yes || true) | "${ANDROID_HOME}/cmdline-tools/latest/bin/sdkmanager" --licenses \
    && (yes || true) | "${ANDROID_HOME}/cmdline-tools/latest/bin/sdkmanager" \
    'tools' 'platform-tools' 'cmake;3.6.4111459' \
    "platforms;android-${platform}" "build-tools;${tools}" \
    "system-images;android-${platform};default;x86_64"

# Set up Android SDK paths.
ENV PATH "${PATH}:${ANDROID_HOME}/emulator:${ANDROID_HOME}/tools:${ANDROID_HOME}/platform-tools:${ANDROID_HOME}/tools/bin"
ENV LD_LIBRARY_PATH "${LD_LIBRARY_PATH}:${ANDROID_HOME}/emulator/lib64:${ANDROID_HOME}/emulator/lib64/qt/lib"

# Install Android NDK
# https://developer.android.com/ndk/downloads
ARG android_ndk_version=r25b
ENV ANDROID_NDK_HOME /opt/android-ndk
RUN mkdir --parents "${ANDROID_NDK_HOME}" \
    && curl --location "https://dl.google.com/android/repository/android-ndk-${android_ndk_version}-linux.zip" > android_ndk.zip \
    && unzip android_ndk.zip -d "${ANDROID_NDK_HOME}" \
    && mv ${ANDROID_NDK_HOME}/android-ndk-${android_ndk_version}/* "${ANDROID_NDK_HOME}" \
    && rm android_ndk.zip

# To make the scripts available to call from everywhere.
ENV PATH "/workspace/scripts:${PATH}"

# Add sourcing of xtask_bash_completion file to .bashrc
RUN echo -e "\n#activate xtask auto-complete\nif [ -f /workspace/.xtask_bash_completion ]; then\n  source /workspace/.xtask_bash_completion \nfi" >> "${HOME}/.bashrc"

# Define alias
RUN echo -e "\nalias ll='ls -l'\n" >> "${HOME}/.bashrc"
