FROM gcr.io/asylo-framework/asylo:buildenv-v0.5.0

RUN apt-get --yes update && apt-get install --yes \
  clang-format \
  clang-tidy \
  curl \
  git \
  libncurses5 \
  python3-pip \
  shellcheck \
  xml2

# Install Node.js and npm.
RUN curl --location https://deb.nodesource.com/setup_12.x | bash -
RUN apt-get install --yes nodejs

# Print version of various tools.
RUN git --version
RUN clang-format -version
RUN shellcheck --version
RUN node --version
RUN npm --version

# Install prettier (via Node.js).
# https://prettier.io/
RUN npm install --global prettier
RUN prettier --version

# Install buildifier.
ARG BAZEL_TOOLS_VERSION=0.29.0
ARG BUILDIFIER_SHA256=4c985c883eafdde9c0e8cf3c8595b8bfdf32e77571c369bf8ddae83b042028d6
ARG BUILDIFIER_DIR=/usr/local/buildifier/bin
ARG BUILDIFIER_BIN=${BUILDIFIER_DIR}/buildifier
RUN mkdir --parents ${BUILDIFIER_DIR}
RUN curl --location https://github.com/bazelbuild/buildtools/releases/download/${BAZEL_TOOLS_VERSION}/buildifier > ${BUILDIFIER_BIN}
RUN sha256sum --binary ${BUILDIFIER_BIN} && echo "${BUILDIFIER_SHA256} *${BUILDIFIER_BIN}" | sha256sum --check
ENV PATH "${BUILDIFIER_DIR}:${PATH}"
RUN chmod +x ${BUILDIFIER_BIN}

# Install Protobuf compiler.
ARG PROTOBUF_VERSION=3.9.1
ARG PROTOBUF_SHA256=77410d08e9a3c1ebb68afc13ee0c0fb4272c01c20bfd289adfb51b1c622bab07
ARG PROTOBUF_DIR=/usr/local/protobuf
ARG PROTOBUF_TEMP=/tmp/protobuf.zip
RUN curl --location https://github.com/protocolbuffers/protobuf/releases/download/v${PROTOBUF_VERSION}/protoc-${PROTOBUF_VERSION}-linux-x86_64.zip > ${PROTOBUF_TEMP}
RUN sha256sum --binary ${PROTOBUF_TEMP} && echo "${PROTOBUF_SHA256} *${PROTOBUF_TEMP}" | sha256sum --check
RUN unzip ${PROTOBUF_TEMP} -d ${PROTOBUF_DIR}
RUN rm ${PROTOBUF_TEMP}
ENV PATH "${PROTOBUF_DIR}/bin:${PATH}"
RUN protoc --version

# Install rustup.
ARG RUSTUP_DIR=/usr/local/cargo
ENV RUSTUP_HOME ${RUSTUP_DIR}
ENV CARGO_HOME ${RUSTUP_DIR}
RUN curl --location https://sh.rustup.rs > /tmp/rustup
RUN sh /tmp/rustup -y --default-toolchain=none
ENV PATH "${RUSTUP_DIR}/bin:${PATH}"
RUN rustup --version
RUN chmod a+rwx ${RUSTUP_DIR}

# Install Rust toolchain.
# We currently need the nightly version in order to be able to compile some of the examples.
ARG RUST_VERSION=nightly-2019-07-18
RUN rustup toolchain install ${RUST_VERSION}
RUN rustup default ${RUST_VERSION}

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install rustfmt, clippy, and the Rust Language Server.
RUN rustup component add \
  clippy \
  rls \
  rust-analysis \
  rust-src \
  rustfmt

# Install embedmd (via Go).
ARG GOLANG_VERSION=1.13.1
ARG GOLANG_SHA256=94f874037b82ea5353f4061e543681a0e79657f787437974214629af8407d124
ARG GOLANG_TEMP=/tmp/golang.tar.gz
ENV GOROOT /usr/local/go
ENV GOPATH ${HOME}/go
RUN mkdir --parents ${GOROOT}
RUN curl --location https://dl.google.com/go/go${GOLANG_VERSION}.linux-amd64.tar.gz > ${GOLANG_TEMP}
RUN sha256sum --binary ${GOLANG_TEMP} && echo "${GOLANG_SHA256} *${GOLANG_TEMP}" | sha256sum --check
RUN tar --extract --gzip --file=${GOLANG_TEMP} --directory=${GOROOT} --strip-components=1
RUN rm ${GOLANG_TEMP}
RUN ${GOROOT}/bin/go get github.com/campoy/embedmd

# Install Emscripten.
ARG EMSCRIPTEN_VERSION=1.39.6
ARG EMSCRIPTEN_COMMIT=6bfbe2a7da68e650054af2d272d2b79307a6ad72
ARG EMSCRIPTEN_SHA256=aa4c3b8f23fd26363f98207674bffcc138105c621c6c8bf12175f6aab1231357
ARG EMSCRIPTEN_DIR=/usr/local/emsdk
ARG EMSCRIPTEN_TEMP=/tmp/emscripten.zip
ENV PATH "${EMSCRIPTEN_DIR}:${EMSCRIPTEN_DIR}/upstream/emscripten:${PATH}"
ENV EMSDK "${EMSCRIPTEN_DIR}"
ENV EM_CONFIG '/tmp/.emscripten'
ENV EM_CACHE '/tmp/.emscripten_cache'
RUN mkdir --parents ${EMSCRIPTEN_DIR}
RUN curl --location https://github.com/emscripten-core/emsdk/archive/${EMSCRIPTEN_COMMIT}.tar.gz > ${EMSCRIPTEN_TEMP}
RUN sha256sum --binary ${EMSCRIPTEN_TEMP} && echo "${EMSCRIPTEN_SHA256} *${EMSCRIPTEN_TEMP}" | sha256sum --check
RUN tar --extract --gzip --file=${EMSCRIPTEN_TEMP} --directory=${EMSCRIPTEN_DIR} --strip-components=1
RUN rm ${EMSCRIPTEN_TEMP}
RUN cd ${EMSCRIPTEN_DIR} \
    && ./emsdk install ${EMSCRIPTEN_VERSION} \
    && ./emsdk activate ${EMSCRIPTEN_VERSION}
# Emscripten config file is automatically generated in `/root/`, so we need to allow access to it
# and put it in a directory with write access, so `emcc` will be able to create `.emscripten_cache.lock`
RUN cp /root/.emscripten "${EM_CONFIG}" \
    && chmod ugo+rw "${EM_CONFIG}" \
    && mkdir -p "${EM_CACHE}" \
    && chmod ugo+rwx "${EM_CACHE}"
