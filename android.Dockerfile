# Use fixed snapshot of Debian to create a deterministic environment.
# Snapshot tags can be found at https://hub.docker.com/r/debian/snapshot/tags?name=bullseye
ARG debian_snapshot=sha256:d647c95797c43e8ef0e0667c4b4acba752ae70385dcf648877903f15c8977da4
FROM debian/snapshot@${debian_snapshot}

RUN apt-get --yes update && \
    apt-get install --no-install-recommends --yes \
    bash-completion \
    bison \
    build-essential \
    curl \
    flex \
    git \
    libisl-dev \
    libmpc-dev \
    libmpfr-dev \
    libncurses5 \
    ocaml-nox \
    openjdk-11-jdk \
    python-dev \
    python2.7-dev \
    python3-dev \
    rsync \
    texinfo \
    vim \
    wget \
    xml2 \
    # `unzip` and `zlib1g-dev` are needed for Bazel.
    unzip \
    zlib1g-dev \
    && apt-get clean \
    && rm --recursive --force /var/lib/apt/lists/* \
    # Print version of various installed tools.
    && git --version

# Use a fixed version of Bazel.
ARG bazel_version=5.3.1
ARG bazel_sha256=1e939b50d90f68d30fa4f3c12dfdf31429b83ddd8076c622429854f64253c23d
ARG bazel_url=https://storage.googleapis.com/bazel-apt/pool/jdk1.8/b/bazel/bazel_${bazel_version}_amd64.deb
RUN curl --location "${bazel_url}" > bazel.deb \
    && sha256sum --binary bazel.deb && echo "${bazel_sha256} *bazel.deb" | sha256sum --check \
    && apt-get install --no-install-recommends --yes ./bazel.deb \
    && rm bazel.deb \
    && apt-get clean \
    && bazel version

# Install Android SDK.
# https://developer.android.com/studio/#downloads
# https://developer.android.com/studio/index.html#command-tools
ARG android_sdk_version=8512546
ENV ANDROID_HOME /opt/android-sdk
RUN mkdir --parents ${ANDROID_HOME} \
    && curl --location https://dl.google.com/android/repository/commandlinetools-linux-"${android_sdk_version}_latest".zip > android_sdk.zip \
    && unzip android_sdk.zip -d ${ANDROID_HOME} \
    && rm android_sdk.zip

# Install Android Platform Tools.
# https://developer.android.com/studio/releases/platform-tools
# https://developer.android.com/studio/releases/platforms
# https://developer.android.com/studio/releases/build-tools
ARG platform=30
ARG tools=30.0.0
RUN ${ANDROID_HOME}/cmdline-tools/bin/sdkmanager --update --sdk_root=${ANDROID_HOME} \
    && yes | ${ANDROID_HOME}/cmdline-tools/bin/sdkmanager --licenses --sdk_root=${ANDROID_HOME} \
    && yes | ${ANDROID_HOME}/cmdline-tools/bin/sdkmanager --sdk_root=${ANDROID_HOME} \
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
RUN mkdir --parents ${ANDROID_NDK_HOME} \
    && curl --location https://dl.google.com/android/repository/android-ndk-"${android_ndk_version}"-linux.zip > android_ndk.zip \
    && unzip android_ndk.zip -d ${ANDROID_NDK_HOME} \
    && mv ${ANDROID_NDK_HOME}/android-ndk-${android_ndk_version}/* ${ANDROID_NDK_HOME} \
    && rm --recursive --force android_ndk.zip
