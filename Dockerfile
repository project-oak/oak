FROM gcr.io/asylo-framework/asylo:buildenv-v0.3.4

RUN apt-get -y update && apt-get install -y git curl clang-format shellcheck
# TODO: remove this when asylo updates their bazel version
RUN apt-get install --only-upgrade bazel

RUN git --version
RUN clang-format -version
RUN shellcheck --version

# Create an user so we don't run this as root.
ARG GID
ARG UID
ARG USERNAME=docker
ARG GROUPNAME=docker

RUN groupadd --force --gid $GID $GROUPNAME
RUN useradd --create-home --uid $UID --gid $GID $USERNAME
USER $USERNAME

# Install protobuf compiler.
ARG PROTOBUF_VERSION=3.7.1
RUN curl -L https://github.com/protocolbuffers/protobuf/releases/download/v${PROTOBUF_VERSION}/protoc-${PROTOBUF_VERSION}-linux-x86_64.zip > /tmp/protobuf.zip
RUN unzip /tmp/protobuf.zip -d ~/protobuf
ENV PATH "/home/$USERNAME/protobuf/bin:$PATH"
RUN protoc --version

# Install Rust compiler.
# TODO: We should pin a specific Rust version rather than just installing the current stable.
RUN curl https://sh.rustup.rs -sSf > /tmp/rustup
RUN sh /tmp/rustup -y
ENV PATH "/home/$USERNAME/.cargo/bin:$PATH"
RUN rustup --version

# Install rustfmt.
RUN rustup component add rustfmt --toolchain stable-x86_64-unknown-linux-gnu

# Install WebAssembly target for Rust.
RUN rustup target add wasm32-unknown-unknown

# Install Rust-clippy.
RUN rustup component add clippy
