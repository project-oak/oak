FROM gcr.io/asylo-framework/asylo:buildenv-v0.4.1

RUN apt-get -y update && apt-get install -y git curl clang-format shellcheck libncurses5 xml2

RUN git --version
RUN clang-format -version
RUN shellcheck --version

# Install buildifier.
ARG BAZEL_VERSION=0.28.0
ARG BUILDIFIER_DIR=/usr/local/buildifier
RUN mkdir -p $BUILDIFIER_DIR/bin
RUN curl -L https://github.com/bazelbuild/buildtools/releases/download/${BAZEL_VERSION}/buildifier > $BUILDIFIER_DIR/bin/buildifier
ENV PATH "$BUILDIFIER_DIR/bin:$PATH"
RUN chmod +x $BUILDIFIER_DIR/bin/buildifier

# Install Protobuf compiler.
ARG PROTOBUF_VERSION=3.9.1
ARG PROTOBUF_DIR=/usr/local/protobuf
RUN curl -L https://github.com/protocolbuffers/protobuf/releases/download/v${PROTOBUF_VERSION}/protoc-${PROTOBUF_VERSION}-linux-x86_64.zip > /tmp/protobuf.zip
RUN unzip /tmp/protobuf.zip -d $PROTOBUF_DIR
ENV PATH "$PROTOBUF_DIR/bin:$PATH"
RUN protoc --version

# Install rustup.
ARG RUSTUP_DIR=/usr/local/cargo
ENV RUSTUP_HOME $RUSTUP_DIR
ENV CARGO_HOME $RUSTUP_DIR
RUN curl https://sh.rustup.rs -sSf > /tmp/rustup
RUN sh /tmp/rustup -y --default-toolchain=none
ENV PATH "$RUSTUP_DIR/bin:$PATH"
RUN rustup --version
RUN chmod a+rwx $RUSTUP_DIR

# Install Rust toolchain.
# We currently need the nightly version in order to be able to compile some of the examples.
ARG RUST_VERSION=nightly-2019-07-18
RUN rustup toolchain install $RUST_VERSION
RUN rustup default $RUST_VERSION

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install rustfmt, clippy, and the Rust Language Server.
RUN rustup component add \
  rustfmt \
  clippy \
  rls \
  rust-analysis \
  rust-src
