# Download Debian-9 (Stretch) with openjdk-8 that is required for Android.
ARG debian_snapshot=stretch-20191118
FROM debian/snapshot:${debian_snapshot}

RUN apt-get update && \
    apt-get install -y \
        bash-completion \
        bison \
        build-essential \
        clang-format \
        clang-tidy \
        curl \
        flex \
        git \
        libisl-dev \
        libmpc-dev \
        libmpfr-dev \
        libncurses5 \
        #libfl2 \
        ocaml-nox \
        #ocamlbuild \
        openjdk-8-jdk \
        python-dev \
        python2.7-dev \
        python3-dev \
        rsync \
        shellcheck \
        texinfo \
        vim \
        wget \
        xml2 \
        zlib1g-dev

# Install NodeJS.
RUN curl -sL https://deb.nodesource.com/setup_12.x  | bash -
RUN apt-get install -y nodejs

RUN git --version
RUN clang-format -version
RUN shellcheck --version
RUN node --version
RUN npm --version

# Install Bazel. 
ARG bazel_version=1.2.1
ARG bazel_sha=4bbb2718d451db5922223fda3aed3810c4ca50f431481e86a7fec4c585f18b1f
ARG bazel_url=https://storage.googleapis.com/bazel-apt/pool/jdk1.8/b/bazel/bazel_${bazel_version}_amd64.deb
RUN wget "${bazel_url}" -nv -o- -O bazel.deb && \
    echo "${bazel_sha}  bazel.deb" > bazel.sha256 && \
    sha256sum --check bazel.sha256 && \
    apt-get install -y ./bazel.deb

# Install prettier (via Node.js).
# https://prettier.io/
RUN npm install --global prettier
RUN prettier --version

# Install buildifier.
ARG BAZEL_TOOLS_VERSION=0.29.0
ARG BUILDIFIER_DIR=/usr/local/buildifier
RUN mkdir -p $BUILDIFIER_DIR/bin
RUN curl -L https://github.com/bazelbuild/buildtools/releases/download/${BAZEL_TOOLS_VERSION}/buildifier > $BUILDIFIER_DIR/bin/buildifier
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

# Install embedmd (via Go).
ARG GOLANG_VERSION=1.13.1
ENV GOROOT /usr/local/go
ENV GOPATH $HOME/go
RUN mkdir -p $GOROOT
RUN curl https://dl.google.com/go/go${GOLANG_VERSION}.linux-amd64.tar.gz | tar xzf - -C ${GOROOT} --strip-components=1
RUN $GOROOT/bin/go get github.com/campoy/embedmd

# Install Android SDK.
# https://developer.android.com/studio/#downloads
ENV ANDROID_HOME /opt/android-sdk
ARG ANDROID_SDK_VERSION=4333796
RUN mkdir -p ${ANDROID_HOME} && cd ${ANDROID_HOME} && \
    wget -q https://dl.google.com/android/repository/sdk-tools-linux-"${ANDROID_SDK_VERSION}".zip && \
    unzip *tools*linux*.zip && \
    rm *tools*linux*.zip

# Install Android Platform Tools.
# https://developer.android.com/studio/releases/platform-tools
# https://developer.android.com/studio/releases/platforms
# https://developer.android.com/studio/releases/build-tools
# 'platforms;android-28' 'build-tools;28.0.3' is the maximal version supported by NDK.
# 'platforms;android-26' 'build-tools;26.0.1' is the minimal verison for Bazel.
ARG PLATFORM='28'
ARG PLATFORM_BAZEL='26'
# TODO: Use 28, since 29 is not supported by NDK
ARG TOOLS='28.0.3'
ARG TOOLS_BAZEL='26.0.1'
RUN cd ${ANDROID_HOME} && \
    ./tools/bin/sdkmanager --update && \
    yes | ./tools/bin/sdkmanager \
        'tools' 'platform-tools' 'cmake;3.6.4111459' \
        "platforms;android-${PLATFORM}" "build-tools;${TOOLS}" \
        "platforms;android-${PLATFORM_BAZEL}" "build-tools;${TOOLS_BAZEL}"

# Install Android NDK
# https://developer.android.com/ndk/downloads
ENV ANDROID_NDK_HOME /opt/android-ndk
ARG ANDROID_NDK_VERSION=r20b
RUN mkdir -p ${ANDROID_NDK_HOME} && cd ${ANDROID_NDK_HOME} && \
    wget -q https://dl.google.com/android/repository/android-ndk-"${ANDROID_NDK_VERSION}"-linux-x86_64.zip && \
	unzip android-ndk*.zip && \
	rm -f android-ndk*.zip && \
    mv android-ndk-r20b/* . && \
    rm -rf android-ndk-r20b

# Default command to run.
CMD ["/bin/bash"]
