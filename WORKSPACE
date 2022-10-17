#
# Copyright 2018 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

workspace(name = "oak")

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

# https://github.com/bazelbuild/bazel-skylib
http_archive(
    name = "bazel_skylib",
    sha256 = "74d544d96f4a5bb630d465ca8bbcfe231e3594e5aae57e1edbf17a6eb3ca2506",
    urls = [
        "https://github.com/bazelbuild/bazel-skylib/releases/download/1.3.0/bazel-skylib-1.3.0.tar.gz",
    ],
)

# https://github.com/bazelbuild/rules_cc
http_archive(
    name = "rules_cc",
    sha256 = "af6cc82d87db94585bceeda2561cb8a9d55ad435318ccb4ddfee18a43580fb5d",
    strip_prefix = "rules_cc-0.0.4",
    urls = ["https://github.com/bazelbuild/rules_cc/releases/download/0.0.4/rules_cc-0.0.4.tar.gz"],
)

http_archive(
    name = "com_google_absl",
    sha256 = "0dbe936c51ad6567446b5a60ea5f2649bdfe5ed4e054972960a0799b74da9d43",
    strip_prefix = "abseil-cpp-b0735979d778a768caee207f01f327535cbd2140",
    urls = [
        # Head commit on 2021-03-04.
        "https://github.com/abseil/abseil-cpp/archive/b0735979d778a768caee207f01f327535cbd2140.zip",
    ],
)

# Go rules.
# https://github.com/bazelbuild/rules_go
http_archive(
    name = "io_bazel_rules_go",
    sha256 = "099a9fb96a376ccbbb7d291ed4ecbdfd42f6bc822ab77ae6f1b5cb9e914e94fa",
    urls = [
        "https://github.com/bazelbuild/rules_go/releases/download/v0.35.0/rules_go-v0.35.0.zip",
    ],
)

load("@io_bazel_rules_go//go:deps.bzl", "go_rules_dependencies")

go_rules_dependencies()

# Java rules.
# https://github.com/bazelbuild/rules_java
http_archive(
    name = "rules_java",
    sha256 = "d974a2d6e1a534856d1b60ad6a15e57f3970d8596fbb0bb17b9ee26ca209332a",
    urls = [
        "https://github.com/bazelbuild/rules_java/releases/download/5.1.0/rules_java-5.1.0.tar.gz",
    ],
)

load("@rules_java//java:repositories.bzl", "rules_java_dependencies", "rules_java_toolchains")

rules_java_dependencies()

rules_java_toolchains()

# Google Protocol Buffers.
# https://github.com/protocolbuffers/protobuf
http_archive(
    name = "com_google_protobuf",
    sha256 = "ce2fbea3c78147a41b2a922485d283137845303e5e1b6cbd7ece94b96ade7031",
    strip_prefix = "protobuf-3.21.7",
    urls = [
        "https://github.com/protocolbuffers/protobuf/archive/v3.21.7.tar.gz",
    ],
)

load("@com_google_protobuf//:protobuf_deps.bzl", "protobuf_deps")

protobuf_deps()

http_archive(
    name = "tink_base",
    sha256 = "536a4ceb3e9e7e35bf52f7cc99838679de8463ab2a1a12b90121c00ee25fe252",
    strip_prefix = "tink-33accb5bcdff71f34d7551a669831ec9a52674aa/",
    urls = [
        # Head commit on 2021-03-02.
        "https://github.com/google/tink/archive/33accb5bcdff71f34d7551a669831ec9a52674aa.zip",
    ],
)

load("@tink_base//:tink_base_deps.bzl", "tink_base_deps")

tink_base_deps()

load("@tink_base//:tink_base_deps_init.bzl", "tink_base_deps_init")

tink_base_deps_init()

# Tink crypto library for Java.
http_archive(
    name = "tink_java",
    patches = [
        # This patch removes Android dependencies from Tink Java libraries.
        # https://github.com/google/tink/issues/507
        "//third_party/google/tink:Remove-android-from-java.patch",
    ],
    sha256 = "5856b0207ffb2cf28dd5c421789ffca3cfeea0680055f455e14bec2f335b1765",
    strip_prefix = "tink-58be99b3c4d09154d12643327f293cc45b2a6a7b/java_src",
    # Commit from 2021-05-19
    urls = [
        "https://github.com/google/tink/archive/58be99b3c4d09154d12643327f293cc45b2a6a7b.tar.gz",
    ],
)

# gRPC.
# https://github.com/grpc/grpc
http_archive(
    name = "com_github_grpc_grpc",
    sha256 = "76900ab068da86378395a8e125b5cc43dfae671e09ff6462ddfef18676e2165a",
    strip_prefix = "grpc-1.50.0",
    urls = ["https://github.com/grpc/grpc/archive/v1.50.0.tar.gz"],
)

# Java gRPC support for Android examples.
# https://github.com/grpc/grpc-java
http_archive(
    name = "io_grpc_grpc_java",
    sha256 = "3658e6a51e6f0fb28adff98a73c8063559641100f5ed79682bc2abfaaf23bfb7",
    strip_prefix = "grpc-java-1.50.0",
    urls = [
        "https://github.com/grpc/grpc-java/archive/v1.50.0.zip",
    ],
)

load("@io_grpc_grpc_java//:repositories.bzl", "IO_GRPC_GRPC_JAVA_ARTIFACTS", "IO_GRPC_GRPC_JAVA_OVERRIDE_TARGETS", "grpc_java_repositories")

grpc_java_repositories()

# External Java rules.
# https://github.com/bazelbuild/rules_jvm_external
http_archive(
    name = "rules_jvm_external",
    sha256 = "735602f50813eb2ea93ca3f5e43b1959bd80b213b836a07a62a29d757670b77b",
    strip_prefix = "rules_jvm_external-4.4.2",
    url = "https://github.com/bazelbuild/rules_jvm_external/archive/4.4.2.zip",
)

# Maven rules.
load("@rules_jvm_external//:defs.bzl", "maven_install")

maven_install(
    artifacts = [
        "org.mockito:mockito-core:3.3.3",
    ] + IO_GRPC_GRPC_JAVA_ARTIFACTS,
    generate_compat_repositories = True,
    override_targets = IO_GRPC_GRPC_JAVA_OVERRIDE_TARGETS,
    repositories = [
        "https://maven.google.com",
        "https://repo1.maven.org/maven2",
    ],
)

load("@maven//:compat.bzl", "compat_repositories")

compat_repositories()

# TensorFlow Lite for Microcontrollers.
# https://github.com/tensorflow/tflite-micro
http_archive(
    name = "com_github_tensorflow_tflite_micro",
    patches = [
        # Replaces debug logging function with an empty stub.
        # TODO(#3297): Replace TFLM logging with Restricted Kernel logging.
        "//third_party/tflite-micro:remove-debug-logging.patch",
    ],
    sha256 = "922425b778d5c9336b69f7f68b5f76ae7e6834e026d981179259993d1de5476d",
    strip_prefix = "tflite-micro-3648cf9003d0e2d5658b1add916000ce09a4b427",
    urls = [
        # Head commit on 2022-10-07.
        "https://github.com/tensorflow/tflite-micro/archive/3648cf9003d0e2d5658b1add916000ce09a4b427.tar.gz",
    ],
)

# TensorFlow dependency.
# https://github.com/bazelbuild/rules_closure
http_archive(
    name = "io_bazel_rules_closure",
    sha256 = "5b00383d08dd71f28503736db0500b6fb4dda47489ff5fc6bed42557c07c6ba9",
    strip_prefix = "rules_closure-308b05b2419edb5c8ee0471b67a40403df940149",
    urls = [
        # Head commit on 2019-06-13.
        "https://github.com/bazelbuild/rules_closure/archive/308b05b2419edb5c8ee0471b67a40403df940149.tar.gz",
    ],
)

# Bazel rules for Android applications.
# https://github.com/bazelbuild/rules_android
http_archive(
    name = "build_bazel_rules_android",
    sha256 = "cd06d15dd8bb59926e4d65f9003bfc20f9da4b2519985c27e190cddc8b7a7806",
    strip_prefix = "rules_android-0.1.1",
    urls = ["https://github.com/bazelbuild/rules_android/archive/v0.1.1.zip"],
)

load("@build_bazel_rules_android//android:rules.bzl", "android_ndk_repository", "android_sdk_repository")

android_sdk_repository(
    name = "androidsdk",
    api_level = 30,
    build_tools_version = "30.0.0",
)

android_ndk_repository(
    name = "androidndk",
    api_level = 28,
)

load("@com_github_grpc_grpc//bazel:grpc_deps.bzl", "grpc_deps")

grpc_deps()

load("@com_github_grpc_grpc//bazel:grpc_extra_deps.bzl", "grpc_extra_deps")

grpc_extra_deps()

load("@com_github_tensorflow_tflite_micro//tensorflow:workspace.bzl", "tf_repositories")

tf_repositories()
