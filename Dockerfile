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

# Install Rust compiler.
# TODO: We should pin a specific Rust version rather than just installing the current stable.
ARG RUSTUP_DIR=/usr/local/cargo
ENV RUSTUP_HOME $RUSTUP_DIR
ENV CARGO_HOME $RUSTUP_DIR
RUN curl https://sh.rustup.rs -sSf > /tmp/rustup
RUN sh /tmp/rustup -y
ENV PATH "$RUSTUP_DIR/bin:$PATH"
RUN rustup --version

# Install rustfmt.
RUN rustup component add rustfmt --toolchain stable-x86_64-unknown-linux-gnu

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install Rust-clippy.
RUN rustup component add clippy
