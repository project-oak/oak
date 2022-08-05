# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/debian/snapshot/tags?name=bullseye
ARG debian_snapshot=sha256:fb7e04be4c79a9eab9c259fd5049f4a1bec321843040184a706bbecdaaacbd32
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

# Getting curl and certificates dependecies.
# We're rate-limiting HTTP requests to 500 kB/s as otherwise we may get timeout errors
# when downloading from snapshot.debian.org.
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes --option Acquire::http::Dl-Limit=500 \
  apt-transport-https \
  build-essential \
  ca-certificates \
  clang-format \
  clang-tidy \
  curl \
  git \
  gnupg2 \
  gnupg-agent \
  libcap-dev \
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

# Add LLDB version 14 for debugging support.
ARG llvm_version=14
RUN echo "deb http://apt.llvm.org/bullseye/ llvm-toolchain-bullseye-$llvm_version main" >> /etc/apt/sources.list.d/llvm.list \
  && curl https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add - \
  && apt-get update --yes \
  && apt-get install --no-install-recommends --yes \
  lldb-${llvm_version} \
  && rm --recursive --force /var/lib/apt/lists/*

# Install a version of docker CLI.
RUN curl --fail --silent --show-error --location https://download.docker.com/linux/debian/gpg | apt-key add -
RUN echo "deb [arch=amd64] https://download.docker.com/linux/debian buster stable"  > /etc/apt/sources.list.d/backports.list \
  && apt-get --yes update \
  && apt-get install --no-install-recommends --yes docker-ce-cli \
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

# Install Ent CLI. We mostly then just use it in order to simplify the logic around fetching
# artifacts by URL and ensuring that their digest is correct, in order to ensure reproducibility.
ARG ent_server_url=https://ent-server-62sa4xcfia-ew.a.run.app
ARG ent_digest=sha256:b2e999bda4c90fc58c924e19787f5f7037f9d48fd83e7deebd06e3e1d5b31e8d
RUN curl --location ${ent_server_url}/raw/${ent_digest} > /usr/local/bin/ent \
  && chmod +x /usr/local/bin/ent \
  && ent

# Use a fixed version of Bazel.
ARG bazel_version=4.2.0
ARG bazel_digest=sha256:89b14fa0d9ce5637f4e0b66df56a531e1e3c50d88614311334d192531cf1e0fa
ARG bazel_url=https://storage.googleapis.com/bazel-apt/pool/jdk1.8/b/bazel/bazel_${bazel_version}_amd64.deb
RUN ent get ${bazel_digest} --url=${bazel_url} > bazel.deb \
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
ARG emscripten_digest=sha256:925dd5ca7dd783d0b367386e81847eaf680d54ae86017c4b5846dea951e17dc9

ARG emscripten_dir=/usr/local/emsdk
ARG emscripten_temp=/tmp/emscripten.zip
RUN mkdir --parents ${emscripten_dir} \
  && ent get ${emscripten_digest} --url=https://github.com/emscripten-core/emsdk/archive/${emscripten_version}.tar.gz > ${emscripten_temp} \
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
ARG golang_version=1.17.7
ARG golang_digest=sha256:02b111284bedbfa35a7e5b74a06082d18632eff824fd144312f6063943d49259
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
RUN go get github.com/campoy/embedmd@97c13d6 \
  && embedmd -v

# Install liche (Markdown link checker) (via Go).
# https://github.com/raviqqe/liche
RUN go get github.com/raviqqe/liche@f9ba5f2 \
  && liche --version

# Install prettier and markdownlint (via Node.js).
# This will use the Node version installed by emscripten.
# https://prettier.io/
# https://github.com/igorshubovych/markdownlint-cli
ARG prettier_version=2.5.1
ARG prettier_plugin_toml_version=0.3.1
ARG markdownlint_version=0.30.0
RUN npm install --global \
  prettier@${prettier_version} \
  prettier-plugin-toml@${prettier_plugin_toml_version} \
  markdownlint-cli@${markdownlint_version} \
  && prettier --version \
  && markdownlint --version

# Install hadolint.
# https://github.com/hadolint/hadolint
ARG hadolint_version=2.8.0
ARG hadolint_digest=sha256:9dfc155139a1e1e9b3b28f3de9907736b9dfe7cead1c3a0ae7ff0158f3191674
ARG hadolint_dir=/usr/local/hadolint/bin
ARG hadolint_bin=${hadolint_dir}/hadolint
ENV PATH "${hadolint_dir}:${PATH}"
RUN mkdir --parents ${hadolint_dir} \
  && ent get ${hadolint_digest} --url=https://github.com/hadolint/hadolint/releases/download/v${hadolint_version}/hadolint-Linux-x86_64 > ${hadolint_bin} \
  && chmod +x ${hadolint_bin} \
  && hadolint --version

# Install buildifier.
# https://github.com/bazelbuild/buildtools/tree/master/buildifier
ARG bazel_tools_version=5.0.0
ARG buildifier_digest=sha256:18a518a4b9b83bb96a115a681099ae6c115217e925a2dacfb263089e3a791b5d
ARG buildifier_dir=/usr/local/buildifier/bin
ARG buildifier_bin=${buildifier_dir}/buildifier
ENV PATH "${buildifier_dir}:${PATH}"
RUN mkdir --parents ${buildifier_dir} \
  && ent get ${buildifier_digest} --url=https://github.com/bazelbuild/buildtools/releases/download/${bazel_tools_version}/buildifier-linux-amd64 > ${buildifier_bin} \
  && chmod +x ${buildifier_bin} \
  && buildifier --version

# Install Protobuf compiler.
ARG protobuf_version=3.19.4
ARG protobuf_digest=sha256:058d29255a08f8661c8096c92961f3676218704cbd516d3916ec468e139cbd87
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
ARG rust_version=nightly-2022-04-22
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
ARG deadlinks_version=0.8.1
RUN cargo install --version=${deadlinks_version} cargo-deadlinks

# Install cargo-fuzz.
# To allow local testing of the fuzzing functionality.
# https://github.com/rust-fuzz/cargo-fuzz
# change cargo-fuzz to the following to avoid a recent failure
# cf. https://github.com/rust-fuzz/cargo-fuzz/pull/277
RUN cargo install --git https://github.com/rust-fuzz/cargo-fuzz/ --rev 8c964bf183c93cd49ad655eb2f3faecf543d0012

# Install Wizer.
# To allow running warmup initialisation on example Wasm modules.
# https://github.com/bytecodealliance/wizer
ARG wizer_version=1.4.0
RUN cargo install --version=${wizer_version} wizer --all-features

# Install crosvm.
# We're not interested in most of the features in crosvm (e.g. wayland support), but GDB support would be nice.
RUN cargo install --git https://chromium.googlesource.com/chromiumos/platform/crosvm/ --rev 31f04e92709980a4ffc56b1631f8b4be437cc2fe crosvm --no-default-features --features gdb

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
ARG crev_version=v0.23.0
ARG crev_location=https://github.com/crev-dev/cargo-crev/releases/download/${crev_version}/cargo-crev-${crev_version}-x86_64-unknown-linux-musl.tar.gz
RUN curl --location ${crev_location} | tar --extract --gzip --directory=${install_dir} --strip-components=1
RUN chmod +x ${install_dir}/cargo-crev

# Install cargo-deny
# https://github.com/EmbarkStudios/cargo-deny
ARG deny_version=0.11.3
ARG deny_location=https://github.com/EmbarkStudios/cargo-deny/releases/download/${deny_version}/cargo-deny-${deny_version}-x86_64-unknown-linux-musl.tar.gz
RUN curl --location ${deny_location} | tar --extract --gzip --directory=${install_dir} --strip-components=1
RUN chmod +x ${install_dir}/cargo-deny

# Install cargo-udeps
# https://github.com/est31/cargo-udeps
ARG udeps_version=v0.1.26
ARG udeps_dir=cargo-udeps-${udeps_version}-x86_64-unknown-linux-gnu
ARG udeps_location=https://github.com/est31/cargo-udeps/releases/download/${udeps_version}/cargo-udeps-${udeps_version}-x86_64-unknown-linux-gnu.tar.gz
RUN curl --location ${udeps_location} | tar --extract --gzip --directory=${install_dir} --strip-components=2 ./${udeps_dir}/cargo-udeps
RUN chmod +x ${install_dir}/cargo-udeps

# Install rust-analyzer
# https://github.com/rust-analyzer/rust-analyzer
ARG rust_analyzer_version=2022-02-14
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

# Install flatbuffers
# https://github.com/google/flatbuffers
# We build the recent flatc version that generates no_std compatible rust code.
# Once a release with that commit has been issued we can revert to using
# a released binary.
# Ref:https://chromium.googlesource.com/external/github.com/google/flatbuffers/+/750dde766990d75f849370582a0f90307c410537
ARG flatc_commit=750dde766990d75f849370582a0f90307c410537
ARG flatbuffer_tmp_dir=/tmp/flatbuffer
# cmake is required to build flatbuffer
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes --option Acquire::http::Dl-Limit=500 \
  cmake \
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*
RUN git clone https://github.com/google/flatbuffers.git ${flatbuffer_tmp_dir}
WORKDIR ${flatbuffer_tmp_dir}
RUN git checkout ${flatc_commit} \
  && cmake -G "Unix Makefiles" -DCMAKE_BUILD_TYPE=Release \
  && make -j \
  && cp ./flatc -d /usr/local/bin/ \
  && chmod +x /usr/local/bin/flatc \
  && rm -rf ${flatbuffer_tmp_dir} \
  && flatc --version

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

# chromium is required to run our tests with wasm-pack
RUN apt-get --yes update \
  && apt-get install --no-install-recommends --yes --option Acquire::http::Dl-Limit=500 \
  chromium \
  chromium-driver \
  && apt-get clean \
  && rm --recursive --force /var/lib/apt/lists/*

# By default, sccache uses `~/.cache/sccache` locally: https://github.com/mozilla/sccache#local.
ENV RUSTC_WRAPPER sccache

# Disable cargo incremental compilation, as it conflicts with sccache: https://github.com/mozilla/sccache#rust
ENV CARGO_INCREMENTAL false

# We use the `docker` user in order to maintain library paths on different
# machines and to make Wasm modules reproducible.
#
# We do not set this as the default user in the Docker image, because we expect its uid not to match
# uid of the host, therefore we need to first fix the uid before actually using the user. This is
# done by /scripts/fix_docker_user_and_run .
RUN useradd --shell=/bin/bash --create-home --user-group docker

# To make the scripts available to call from everywhere.
ENV PATH "/workspace/scripts:${PATH}"

# Add sourcing of xtask_bash_completion file to .bashrc
RUN echo -e "\n#activate xtask auto-complete\nif [ -f /workspace/.xtask_bash_completion ]; then\n  source /workspace/.xtask_bash_completion \nfi" >> /home/docker/.bashrc

# Define alias
RUN echo -e "\nalias ll='ls -l'\n" >> /home/docker/.bashrc
