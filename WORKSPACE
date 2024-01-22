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

# The `name` argument in all `http_archive` rules should be equal to the
# WORKSPACE name of the corresponding library.

# Google Abseil.
# https://github.com/abseil/abseil-cpp

COM_GOOGLE_ABSL_TAG = "20230802.1"

http_archive(
    name = "com_google_absl",
    sha256 = "987ce98f02eefbaf930d6e38ab16aa05737234d7afbab2d5c4ea7adbe50c28ed",
    strip_prefix = "abseil-cpp-{}".format(COM_GOOGLE_ABSL_TAG),
    urls = [
        "https://github.com/abseil/abseil-cpp/archive/refs/tags/{}.tar.gz".format(COM_GOOGLE_ABSL_TAG),
    ],
)

# BoringSSL.
# https://github.com/google/boringssl
http_archive(
    name = "boringssl",
    sha256 = "b6dd308895eea9e1f0d3f503b7210141f75ba6817c78b4057406ee8f0a042504",
    strip_prefix = "boringssl-44cc20b4a0227b8913dc5f9e063443cb05e4134d",
    urls = [
        # Head commit on 2023-06-14.
        "https://github.com/google/boringssl/archive/44cc20b4a0227b8913dc5f9e063443cb05e4134d.zip",
    ],
)

# GoogleTest
# https://github.com/google/googletest
http_archive(
    name = "com_google_googletest",
    sha256 = "983a7f2f4cc2a4d75d94ee06300c46a657291fba965e355d11ab3b6965a7b0e5",
    strip_prefix = "googletest-b796f7d44681514f58a683a3a71ff17c94edb0c1",
    urls = [
        # Latest commit for version 1.13.0. This requires at least C++14.
        "https://github.com/google/googletest/archive/b796f7d44681514f58a683a3a71ff17c94edb0c1.zip",
    ],
)

# Google Protocol Buffers.
# https://github.com/protocolbuffers/protobuf
COM_GOOGLE_PROTOBUF_TAG = "25.2"

http_archive(
    name = "com_google_protobuf",
    sha256 = "8ff511a64fc46ee792d3fe49a5a1bcad6f7dc50dfbba5a28b0e5b979c17f9871",
    strip_prefix = "protobuf-{}".format(COM_GOOGLE_PROTOBUF_TAG),
    urls = [
        "https://github.com/protocolbuffers/protobuf/releases/download/v{}/protobuf-{}.tar.gz".format(COM_GOOGLE_PROTOBUF_TAG, COM_GOOGLE_PROTOBUF_TAG),
    ],
)

load("@com_google_protobuf//:protobuf_deps.bzl", "protobuf_deps")

protobuf_deps()

RULES_JVM_EXTERNAL_TAG = "6.0"

# External Java rules.
# https://github.com/bazelbuild/rules_jvm_external
http_archive(
    name = "rules_jvm_external",
    sha256 = "85fd6bad58ac76cc3a27c8e051e4255ff9ccd8c92ba879670d195622e7c0a9b7",
    strip_prefix = "rules_jvm_external-{}".format(RULES_JVM_EXTERNAL_TAG),
    urls = [
        "https://github.com/bazelbuild/rules_jvm_external/releases/download/{}/rules_jvm_external-{}.tar.gz".format(RULES_JVM_EXTERNAL_TAG, RULES_JVM_EXTERNAL_TAG),
    ],
)

# C++ gRPC support.
# https://github.com/grpc/grpc
COM_GITHUB_GRPC_GRPC_TAG = "1.60.0"

http_archive(
    name = "com_github_grpc_grpc",
    sha256 = "437068b8b777d3b339da94d3498f1dc20642ac9bfa76db43abdd522186b1542b",
    strip_prefix = "grpc-{}".format(COM_GITHUB_GRPC_GRPC_TAG),
    urls = [
        "https://github.com/grpc/grpc/archive/refs/tags/v{}.tar.gz".format(COM_GITHUB_GRPC_GRPC_TAG),
    ],
)

load("@com_github_grpc_grpc//bazel:grpc_deps.bzl", "grpc_deps")

grpc_deps()

load("@com_github_grpc_grpc//bazel:grpc_extra_deps.bzl", "grpc_extra_deps")

grpc_extra_deps()

# Java gRPC support.
# https://github.com/grpc/grpc-java
# Use the same version as the C++ gRPC library.
http_archive(
    name = "io_grpc_grpc_java",
    sha256 = "02c9a7f9400d4e29c7e55667851083a9f695935081787079a834da312129bf97",
    strip_prefix = "grpc-java-{}".format(COM_GITHUB_GRPC_GRPC_TAG),
    urls = [
        "https://github.com/grpc/grpc-java/archive/refs/tags/v{}.tar.gz".format(COM_GITHUB_GRPC_GRPC_TAG),
    ],
)

load("@io_grpc_grpc_java//:repositories.bzl", "IO_GRPC_GRPC_JAVA_ARTIFACTS", "IO_GRPC_GRPC_JAVA_OVERRIDE_TARGETS", "grpc_java_repositories")

grpc_java_repositories()

load("@rules_jvm_external//:repositories.bzl", "rules_jvm_external_deps")

rules_jvm_external_deps()

load("@rules_jvm_external//:setup.bzl", "rules_jvm_external_setup")

rules_jvm_external_setup()

# Maven rules.
load("@rules_jvm_external//:defs.bzl", "maven_install")

maven_install(
    artifacts = [
        "org.mockito:mockito-core:3.3.3",
        "org.assertj:assertj-core:3.12.1",
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

load(
    "@bazel_tools//tools/build_defs/repo:git.bzl",
    "git_repository",
)

# Run clang-tidy on C++ code with the following command:
# bazel build //cc/... \
#   --aspects=@bazel_clang_tidy//clang_tidy:clang_tidy.bzl%clang_tidy_aspect \
#   --output_groups=report
git_repository(
    name = "bazel_clang_tidy",
    commit = "f43f9d61c201b314c62a3ebcf2d4a37f1a3b06f7",
    remote = "https://github.com/erenon/bazel_clang_tidy.git",
)

# Bazel rules for building OCI images and runtime bundles.
http_archive(
    name = "rules_oci",
    sha256 = "686f871f9697e08877b85ea6c16c8d48f911bf466c3aeaf108ca0ab2603c7306",
    strip_prefix = "rules_oci-1.5.1",
    url = "https://github.com/bazel-contrib/rules_oci/releases/download/v1.5.1/rules_oci-v1.5.1.tar.gz",
)

load("@rules_oci//oci:dependencies.bzl", "rules_oci_dependencies")

rules_oci_dependencies()

load("@rules_oci//oci:repositories.bzl", "LATEST_CRANE_VERSION", "LATEST_ZOT_VERSION", "oci_register_toolchains")

oci_register_toolchains(
    name = "oci",
    crane_version = LATEST_CRANE_VERSION,
    zot_version = LATEST_ZOT_VERSION,
)

load("@rules_oci//oci:pull.bzl", "oci_pull")

oci_pull(
    name = "distroless_cc_debian12",
    digest = "sha256:6714977f9f02632c31377650c15d89a7efaebf43bab0f37c712c30fc01edb973",
    image = "gcr.io/distroless/cc-debian12",
    platforms = ["linux/amd64"],
)

load("@//bazel:repositories.bzl", "oak_toolchain_repositories")

oak_toolchain_repositories()

# Register a hermetic C++ toolchain to ensure that binaries use a glibc version supported by
# distroless images. The glibc version provided by nix may be too new.
# This (currently) needs to be loaded after rules_oci because it defaults to using an older version
# of aspect-build/bazel-lib.
http_archive(
    name = "aspect_gcc_toolchain",
    sha256 = "3341394b1376fb96a87ac3ca01c582f7f18e7dc5e16e8cf40880a31dd7ac0e1e",
    strip_prefix = "gcc-toolchain-0.4.2",
    urls = [
        "https://github.com/aspect-build/gcc-toolchain/archive/refs/tags/0.4.2.tar.gz",
    ],
)

load("@aspect_gcc_toolchain//toolchain:repositories.bzl", "gcc_toolchain_dependencies")

gcc_toolchain_dependencies()

load("@aspect_gcc_toolchain//toolchain:defs.bzl", "ARCHS", "gcc_register_toolchain")

gcc_register_toolchain(
    name = "gcc_toolchain_x86_64",
    target_arch = ARCHS.x86_64,
)
