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
        ocaml-nox \
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

RUN git --version
RUN clang-format -version
RUN shellcheck --version

# Install Bazel. 
ARG bazel_version=1.2.1
ARG bazel_sha=4bbb2718d451db5922223fda3aed3810c4ca50f431481e86a7fec4c585f18b1f
ARG bazel_url=https://storage.googleapis.com/bazel-apt/pool/jdk1.8/b/bazel/bazel_${bazel_version}_amd64.deb
RUN wget "${bazel_url}" -nv -o- -O bazel.deb && \
    echo "${bazel_sha}  bazel.deb" > bazel.sha256 && \
    sha256sum --check bazel.sha256 && \
    apt-get install -y ./bazel.deb

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
# '28.0.3' is the maximal version supported by NDK.
ARG PLATFORM='28'
ARG TOOLS='28.0.3'
RUN cd ${ANDROID_HOME}/tools/bin && \
    ./sdkmanager --update && \
    yes | ./sdkmanager --licenses && \
    yes | ./sdkmanager \
        'tools' 'platform-tools' 'cmake;3.6.4111459' \
        "platforms;android-${PLATFORM}" "build-tools;${TOOLS}" \
        "system-images;android-${PLATFORM};default;x86_64"

# Set up Android SDK paths.
ENV PATH ${PATH}:${ANDROID_HOME}/emulator:${ANDROID_HOME}/tools:${ANDROID_HOME}/platform-tools:${ANDROID_HOME}/tools/bin
ENV LD_LIBRARY_PATH ${LD_LIBRARY_PATH}:${ANDROID_HOME}/emulator/lib64:${ANDROID_HOME}/emulator/lib64/qt/lib

# Create an Android emulator.
# `no` is used to opt-out from custom hardware profile.
RUN cd ${ANDROID_HOME}/tools/bin && \
    echo no | ./avdmanager create avd \
        -n "android-${PLATFORM}-x86_64" \
        -k "system-images;android-${PLATFORM};default;x86_64" \
        -b x86_64

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
