FROM gcr.io/asylo-framework/asylo:buildenv-v0.4.0

RUN apt-get -y update && apt-get install -y git curl clang-format shellcheck

RUN git --version
RUN clang-format -version
RUN shellcheck --version

# Install Protobuf compiler.
ARG PROTOBUF_VERSION=3.7.1
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

# Install Rust toolchain.
ARG RUST_VERSION=1.35.0
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
