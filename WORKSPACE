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

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

# The `name` argument in all `http_archive` rules should be equal to the
# WORKSPACE name of the corresponding library.

# Google Abseil.
# https://github.com/abseil/abseil-cpp
http_archive(
    name = "com_google_absl",
    sha256 = "3c743204df78366ad2eaf236d6631d83f6bc928d1705dd0000b872e53b73dc6a",
    strip_prefix = "abseil-cpp-20240116.1",
    urls = [
        # Abseil LTS 20240116.1
        "https://github.com/abseil/abseil-cpp/archive/refs/tags/20240116.1.tar.gz",
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

# C++ gRPC support.
# https://github.com/grpc/grpc
http_archive(
    name = "com_github_grpc_grpc",
    sha256 = "f40bde4ce2f31760f65dc49a2f50876f59077026494e67dccf23992548b1b04f",
    strip_prefix = "grpc-1.62.0",
    urls = [
        "https://github.com/grpc/grpc/archive/refs/tags/v1.62.0.tar.gz",
    ],
)

load("@com_github_grpc_grpc//bazel:grpc_deps.bzl", "grpc_deps")

grpc_deps()

load("@com_github_grpc_grpc//bazel:grpc_extra_deps.bzl", "grpc_extra_deps")

grpc_extra_deps()

# Java gRPC support.
# https://github.com/grpc/grpc-java
http_archive(
    name = "io_grpc_grpc_java",
    sha256 = "4a37fbdf88c8344e14a12bb261aa3eb1401fa47cfc312fb82260592aa993171a",
    strip_prefix = "grpc-java-1.62.0",
    urls = [
        "https://github.com/grpc/grpc-java/archive/refs/tags/v1.62.0.tar.gz",
    ],
)

load("@io_grpc_grpc_java//:repositories.bzl", "IO_GRPC_GRPC_JAVA_ARTIFACTS", "IO_GRPC_GRPC_JAVA_OVERRIDE_TARGETS", "grpc_java_repositories")

grpc_java_repositories()

### --- Base Proto Support --- ###
http_archive(
    name = "rules_proto",
    sha256 = "dc3fb206a2cb3441b485eb1e423165b231235a1ea9b031b4433cf7bc1fa460dd",
    strip_prefix = "rules_proto-5.3.0-21.7",
    urls = [
        "https://github.com/bazelbuild/rules_proto/archive/refs/tags/5.3.0-21.7.tar.gz",
    ],
)

load("@rules_proto//proto:repositories.bzl", "rules_proto_dependencies", "rules_proto_toolchains")

rules_proto_dependencies()

rules_proto_toolchains()

# External Java rules.
# https://github.com/bazelbuild/rules_jvm_external
http_archive(
    name = "rules_jvm_external",
    sha256 = "f86fd42a809e1871ca0aabe89db0d440451219c3ce46c58da240c7dcdc00125f",
    strip_prefix = "rules_jvm_external-5.2",
    urls = [
        # Rules Java v5.2 (2023-04-13).
        "https://github.com/bazelbuild/rules_jvm_external/releases/download/5.2/rules_jvm_external-5.2.tar.gz",
    ],
)

load("@rules_jvm_external//:repositories.bzl", "rules_jvm_external_deps")

rules_jvm_external_deps()

load("@rules_jvm_external//:setup.bzl", "rules_jvm_external_setup")

rules_jvm_external_setup()

# Maven rules.
load("@rules_jvm_external//:defs.bzl", "maven_install")

maven_install(
    artifacts = [
        "co.nstant.in:cbor:0.9",
        "com.google.crypto.tink:tink:1.12.0",
        "org.assertj:assertj-core:3.12.1",
        "org.bouncycastle:bcpkix-jdk18on:1.77",
        "org.bouncycastle:bcprov-jdk18on:1.77",
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
    sha256 = "5816f4198184a1e0e682d7e6b817331219929401e2f18358fac7f7b172737976",
    strip_prefix = "rules_foreign_cc-0.10.0",
    url = "https://github.com/bazelbuild/rules_foreign_cc/archive/refs/tags/0.10.0.tar.gz",
)

load("@rules_foreign_cc//foreign_cc:repositories.bzl", "rules_foreign_cc_dependencies")

# This sets up some common toolchains for building targets. For more details, please see
# https://bazelbuild.github.io/rules_foreign_cc/0.9.0/flatten.html#rules_foreign_cc_dependencies
rules_foreign_cc_dependencies()

http_archive(
    name = "rules_kotlin",
    sha256 = "d9898c3250e0442436eeabde4e194c30d6c76a4a97f517b18cefdfd4e345725a",
    url = "https://github.com/bazelbuild/rules_kotlin/releases/download/v1.9.1/rules_kotlin-v1.9.1.tar.gz",
)

load("@rules_kotlin//kotlin:repositories.bzl", "kotlin_repositories")

kotlin_repositories()  # if you want the default. Otherwise see custom kotlinc distribution below

load("@rules_kotlin//kotlin:core.bzl", "kt_register_toolchains")

kt_register_toolchains()  # to use the default toolchain, otherwise see toolchains below

# C++ CBOR support.
# https://android.googlesource.com/platform/external/libcppbor
git_repository(
    name = "libcppbor",
    build_file = "@//:third_party/google/libcppbor/BUILD",
    # Head commit on 2023-12-04.
    commit = "20d2be8672d24bfb441d075f82cc317d17d601f8",
    patches = [
        "@//:third_party/google/libcppbor/remove_macro.patch",
    ],
    remote = "https://android.googlesource.com/platform/external/libcppbor",
)

http_archive(
    name = "cose_lib",
    build_file = "@//:third_party/BUILD.cose_lib",
    sha256 = "e41a068b573bb07ed2a50cb3c39ae10995977cad82e24a7873223277e7fdb4e5",
    strip_prefix = "cose-lib-2023.09.08",
    url = "https://github.com/android/cose-lib/archive/refs/tags/v2023.09.08.tar.gz",
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
    sha256 = "56d5499025d67a6b86b2e6ebae5232c72104ae682b5a21287770bd3bf0661abf",
    strip_prefix = "rules_oci-1.7.5",
    url = "https://github.com/bazel-contrib/rules_oci/releases/download/v1.7.5/rules_oci-v1.7.5.tar.gz",
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

oci_pull(
    name = "oak_containers_sysimage_base",
    digest = "sha256:a0770fe3c246cf54112179011907c6bc5c2948c302d01c289cdda855e6f66702",
    image = "europe-west2-docker.pkg.dev/oak-ci/oak-containers-sysimage-base/oak-containers-sysimage-base",
)

oci_pull(
    name = "oak_containers_nvidia_sysimage_base",
    digest = "sha256:9c5c0385c9c9902aa21ef4206729dfebb7b4d1b17ae1fc849de14d80d7c20482",
    image = "europe-west2-docker.pkg.dev/oak-ci/oak-containers-sysimage-base/oak-containers-nvidia-sysimage-base",
)

load("@aspect_bazel_lib//lib:repositories.bzl", "register_expand_template_toolchains")

register_expand_template_toolchains()

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

# --- Rust support ---

load("@rules_cc//cc:repositories.bzl", "rules_cc_dependencies", "rules_cc_toolchains")

rules_cc_dependencies()

rules_cc_toolchains()

register_toolchains(
    "//bazel/toolchains:x86_64_unknown_none_toolchain",
)

# rules_rust

_RUST_NIGHTLY_VERSION = "nightly/2024-02-01"

_RUST_VERSIONS = [
    "1.76.0",
    _RUST_NIGHTLY_VERSION,
]

http_archive(
    name = "rules_rust",
    integrity = "sha256-ww398ehv1QZQp26mRbOkXy8AZnsGGHpoXpVU4WfKl+4=",
    urls = ["https://github.com/bazelbuild/rules_rust/releases/download/0.40.0/rules_rust-v0.40.0.tar.gz"],
)

load("@rules_rust//rust:repositories.bzl", "rules_rust_dependencies", "rust_register_toolchains", "rust_repository_set")

rules_rust_dependencies()

rust_register_toolchains(
    edition = "2021",
    versions = _RUST_VERSIONS,
)

_BARE_METAL_RUSTC_FLAGS = [
    "-C",
    "relocation-model=static",
    "-C",
    "target-feature=+sse,+sse2,+ssse3,+sse4.1,+sse4.2,+avx,+avx2,+rdrand,-soft-float",
]

# Creates remote repositories for Rust toolchains, required for cross-compiling.
rust_repository_set(
    name = "rust_toolchain_repo",
    edition = "2021",
    exec_triple = "x86_64-unknown-linux-gnu",
    extra_rustc_flags = {
        "x86_64-unknown-none": _BARE_METAL_RUSTC_FLAGS,
    },
    extra_target_triples = {
        "x86_64-unknown-none": [
            "@platforms//cpu:x86_64",
            "@platforms//os:none",
        ],
    },
    versions = _RUST_VERSIONS,
)

load("//bazel/crates:repositories.bzl", "create_oak_crate_repositories")

create_oak_crate_repositories()

load("//bazel/crates:crates.bzl", "load_oak_crate_repositories")

load_oak_crate_repositories()

load("//bazel/tools/prost:deps.bzl", "prost_toolchain_crates")

prost_toolchain_crates()

load("//bazel/tools/prost:defs.bzl", "setup_prost_toolchain")

setup_prost_toolchain()

# IDE support via rust-analyzer for bazel-only projects.
# https://bazelbuild.github.io/rules_rust/rust_analyzer.html
#
# You can re-generate the rust-project.json file using:
# bazel run @rules_rust//tools/rust_analyzer:gen_rust_project
#
# It should not be committed.
#
# VSCode users: There's a task included in .vscode/tasks.json that should
# automatically do this for you when needed.
load("@rules_rust//tools/rust_analyzer:deps.bzl", "rust_analyzer_dependencies")

rust_analyzer_dependencies()
