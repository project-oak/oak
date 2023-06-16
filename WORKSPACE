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

# Google Abseil.
# https://github.com/abseil/abseil-cpp
http_archive(
    name = "com_google_absl",
    sha256 = "91ac87d30cc6d79f9ab974c51874a704de9c2647c40f6932597329a282217ba8",
    strip_prefix = "abseil-cpp-20220623.1",
    urls = [
        "https://github.com/abseil/abseil-cpp/archive/20220623.1.tar.gz",
    ],
)

# BoringSSL.
# https://github.com/google/boringssl
http_archive(
    name = "com_google_boringssl",
    #sha256 = "37d6a208168f5e4095129593071128d3a4584051e3e2dcc03e39672bf38e61b5",
    #strip_prefix = "boringssl-refs_heads_master-with-bazel",
    urls = [
        # Head commit on 2023-06-05.
        "https://boringssl.googlesource.com/boringssl/+archive/1d9679fc012ef5043489246053d2eafb997b95ba.tar.gz",
    ],
)

# GoogleTest
# https://github.com/google/googletest
http_archive(
    name = "com_google_googletest",
    strip_prefix = "googletest-b796f7d44681514f58a683a3a71ff17c94edb0c1",
    urls = [
        # Latest commit for version 1.13.0. This requires at least C++14.
        "https://github.com/google/googletest/archive/b796f7d44681514f58a683a3a71ff17c94edb0c1.zip",
    ],
)

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

# Bazel rules for Android applications.
# https://github.com/bazelbuild/rules_android
http_archive(
    name = "build_bazel_rules_android",
    sha256 = "cd06d15dd8bb59926e4d65f9003bfc20f9da4b2519985c27e190cddc8b7a7806",
    strip_prefix = "rules_android-0.1.1",
    urls = ["https://github.com/bazelbuild/rules_android/archive/v0.1.1.zip"],
)

load("@build_bazel_rules_android//android:rules.bzl", "android_sdk_repository")

android_sdk_repository(
    name = "androidsdk",
    api_level = 30,
    build_tools_version = "30.0.0",
)

http_archive(
    name = "rules_foreign_cc",
    sha256 = "2a4d07cd64b0719b39a7c12218a3e507672b82a97b98c6a89d38565894cf7c51",
    strip_prefix = "rules_foreign_cc-0.9.0",
    url = "https://github.com/bazelbuild/rules_foreign_cc/archive/refs/tags/0.9.0.tar.gz",
)

load("@rules_foreign_cc//foreign_cc:repositories.bzl", "rules_foreign_cc_dependencies")

# This sets up some common toolchains for building targets. For more details, please see
# https://bazelbuild.github.io/rules_foreign_cc/0.9.0/flatten.html#rules_foreign_cc_dependencies
rules_foreign_cc_dependencies()

http_archive(
    name = "x86_64-unknown-oak",
    build_file = "//toolchain:x86_64-unknown-oak.BUILD",
    sha256 = "52e8d0a5ef7fdfe5981e4fb98576064d70ce75b82654ec50ff80d2de58a71f33",
    strip_prefix = "toolchain",
    type = "tar.bz2",
    url = "https://ent-server-62sa4xcfia-ew.a.run.app/raw/sha256:52e8d0a5ef7fdfe5981e4fb98576064d70ce75b82654ec50ff80d2de58a71f33",
)

register_toolchains("//toolchain:oak")
