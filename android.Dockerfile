# Download Debian-9 (Stretch) with openjdk-8 that is required for Android.
ARG debian_snapshot=stretch-20200327
FROM debian/snapshot:${debian_snapshot}

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
    openjdk-8-jdk \
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
ARG bazel_version=3.0.0
ARG bazel_sha256=dfa79c10bbfa39cd778e1813a273fd3236beb495497baa046f26d393c58bdc35
ARG bazel_url=https://storage.googleapis.com/bazel-apt/pool/jdk1.8/b/bazel/bazel_${bazel_version}_amd64.deb
RUN curl --location "${bazel_url}" > bazel.deb \
    && sha256sum --binary bazel.deb && echo "${bazel_sha256} *bazel.deb" | sha256sum --check \
    && apt-get install --no-install-recommends --yes ./bazel.deb \
    && rm bazel.deb \
    && apt-get clean \
    && bazel version

# Install Android SDK.
# https://developer.android.com/studio/#downloads
ARG android_sdk_version=4333796
ENV ANDROID_HOME /opt/android-sdk
RUN mkdir --parents ${ANDROID_HOME} \
    && curl --location https://dl.google.com/android/repository/sdk-tools-linux-"${android_sdk_version}".zip > android_sdk.zip \
    && unzip android_sdk.zip -d ${ANDROID_HOME} \
    && rm android_sdk.zip

# Install Android Platform Tools.
# https://developer.android.com/studio/releases/platform-tools
# https://developer.android.com/studio/releases/platforms
# https://developer.android.com/studio/releases/build-tools
# '28.0.3' is the maximal version supported by NDK.
ARG platform=28
ARG tools=28.0.3
RUN ${ANDROID_HOME}/tools/bin/sdkmanager --update \
    && yes | ${ANDROID_HOME}/tools/bin/sdkmanager --licenses \
    && yes | ${ANDROID_HOME}/tools/bin/sdkmanager \
    'tools' 'platform-tools' 'cmake;3.6.4111459' \
    "platforms;android-${platform}" "build-tools;${tools}" \
    "system-images;android-${platform};default;x86_64"

# Set up Android SDK paths.
ENV PATH "${PATH}:${ANDROID_HOME}/emulator:${ANDROID_HOME}/tools:${ANDROID_HOME}/platform-tools:${ANDROID_HOME}/tools/bin"
ENV LD_LIBRARY_PATH "${LD_LIBRARY_PATH}:${ANDROID_HOME}/emulator/lib64:${ANDROID_HOME}/emulator/lib64/qt/lib"

# Create an Android emulator.
# `no` is used to opt-out from custom hardware profile.
RUN echo no | ${ANDROID_HOME}/tools/bin/avdmanager create avd \
    -n "android-${platform}-x86_64" \
    -k "system-images;android-${platform};default;x86_64" \
    -b x86_64

# Install Android NDK
# https://developer.android.com/ndk/downloads
ARG android_ndk_version=r20b
ENV ANDROID_NDK_HOME /opt/android-ndk
RUN mkdir --parents ${ANDROID_NDK_HOME} \
    && curl --location https://dl.google.com/android/repository/android-ndk-"${android_ndk_version}"-linux-x86_64.zip > android_ndk.zip \
    && unzip android_ndk.zip -d ${ANDROID_NDK_HOME} \
    && mv ${ANDROID_NDK_HOME}/android-ndk-${android_ndk_version}/* ${ANDROID_NDK_HOME} \
    && rm --recursive --force android_ndk.zip
