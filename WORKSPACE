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
load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive", "http_file")

# The `name` argument in all `http_archive` rules should be equal to the
# WORKSPACE name of the corresponding library.

# Java gRPC support.
# https://github.com/grpc/grpc-java
http_archive(
    name = "io_grpc_grpc_java",
    sha256 = "524a3d687f06ffd1c6ab66dbbb5de5b9f6adaa662570aa56e553d86c2065eb31",
    strip_prefix = "grpc-java-1.72.0",
    urls = [
        "https://github.com/grpc/grpc-java/archive/refs/tags/v1.72.0.tar.gz",
    ],
)

load("@io_grpc_grpc_java//:repositories.bzl", "IO_GRPC_GRPC_JAVA_ARTIFACTS", "IO_GRPC_GRPC_JAVA_OVERRIDE_TARGETS", "grpc_java_repositories")

grpc_java_repositories()

# Kotlin gRPC
http_archive(
    name = "com_github_grpc_grpc_kotlin",
    repo_mapping = {"@io_bazel_rules_kotlin": "@rules_kotlin"},
    sha256 = "cf7975a6edd62a3605f84636804d44e6755db6f7fde3d0e0ab8e1a2837c6e2b5",
    strip_prefix = "grpc-kotlin-1.4.2",
    url = "https://github.com/grpc/grpc-kotlin/archive/refs/tags/v1.4.2.tar.gz",
)

load(
    "@com_github_grpc_grpc_kotlin//:repositories.bzl",
    "IO_GRPC_GRPC_KOTLIN_ARTIFACTS",
    "IO_GRPC_GRPC_KOTLIN_OVERRIDE_TARGETS",
    "grpc_kt_repositories",
)

grpc_kt_repositories()

# External Java rules.
# https://github.com/bazelbuild/rules_jvm_external
http_archive(
    name = "rules_jvm_external",
    sha256 = "a1e351607f04fed296ba33c4977d3fe2a615ed50df7896676b67aac993c53c18",
    strip_prefix = "rules_jvm_external-6.7",
    urls = [
        # Rules Java v5.2 (2023-04-13).
        "https://github.com/bazelbuild/rules_jvm_external/releases/download/6.7/rules_jvm_external-6.7.tar.gz",
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
        "com.google.errorprone:error_prone_annotations:2.38.0",
        "com.google.flogger:flogger-system-backend:0.8",
        "com.google.flogger:google-extensions:0.8",
        "com.google.protobuf:protobuf-kotlin:3.18.0",
        "javax.inject:javax.inject:1",
        "org.assertj:assertj-core:3.12.1",
        "org.bouncycastle:bcpkix-jdk18on:1.77",
        "org.bouncycastle:bcprov-jdk18on:1.77",
        "org.jetbrains.kotlin:kotlin-test:2.0.0",
        "org.jetbrains.kotlinx:kotlinx-coroutines-core:1.7.3",
        "org.jetbrains.kotlinx:kotlinx-coroutines-test:1.7.3",
        "org.mockito:mockito-core:3.3.3",
        "org.mockito.kotlin:mockito-kotlin:4.1.0",
    ] + IO_GRPC_GRPC_JAVA_ARTIFACTS + IO_GRPC_GRPC_KOTLIN_ARTIFACTS,
    generate_compat_repositories = True,
    override_targets = dict(
        IO_GRPC_GRPC_KOTLIN_OVERRIDE_TARGETS.items() +
        IO_GRPC_GRPC_JAVA_OVERRIDE_TARGETS.items(),
    ),
    repositories = [
        "https://maven.google.com",
        "https://repo1.maven.org/maven2",
    ],
)

load("@maven//:compat.bzl", "compat_repositories")

compat_repositories()

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

# C++ CBOR support.
# https://android.googlesource.com/platform/external/libcppbor
git_repository(
    name = "libcppbor",
    build_file = "@//:third_party/google/libcppbor/BUILD",
    # Head commit on 202505-09
    commit = "b1b998be4ec447f3086e7fd6a7f78eaec66a1c45",
    patches = [
        "@//:third_party/google/libcppbor/remove_macro.patch",
        "@//:third_party/google/libcppbor/limits.patch",
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

# This is the base docker image we use to bundle example apps like hello world
# enclave apps. We don't build these, we pull them from the existing repo.
#
# E.g.: //oak_containers/examples/hello_world/enclave_app:bundle . You can find
# these images at: gcr.io/distroless/cc-debian12 . We do not need root access
# so you can search with ":nonroot" (gcr.io/distroless/cc-debian12:nonroot) or
# "latest" (gcr.io/distroless/cc-debian12:latest). Note files tagged as ".sig"
# or ".att" do not contain images. You can find a given digest (like the one
# below) at http://gcr.io/distroless/cc-debian12@{digest} where {digest}
# includes the "sha256:" bit.
oci_pull(
    name = "distroless_cc_debian12",
    digest = "sha256:6714977f9f02632c31377650c15d89a7efaebf43bab0f37c712c30fc01edb973",
    image = "gcr.io/distroless/cc-debian12",
    platforms = ["linux/amd64"],
)

load("@aspect_bazel_lib//lib:repositories.bzl", "register_expand_template_toolchains")

register_expand_template_toolchains()

load("@//bazel:repositories.bzl", "oak_toolchain_repositories")

oak_toolchain_repositories()

# Expected hashes for our base image tarballs
SYSROOT_SHA256 = "d6f608cf14b27bd4ae68f135b601b86bb9157a1a7a8fc08e43d7ff4ab7a18665"

BASE_IMAGE_SHA256 = "f539ecab633fa0a760ec49e917a0719f2d3ffc1eb6fe7853d518d17699fa035e"

NVIDIA_BASE_IMAGE_SHA256 = "10e665a269b79aef1e12a45a60abd1bf4638edae3bad0c41cec764ceacbfe0a9"

# Experimental sysroot for the build toolchain, based on Oak Containers sysimage.
#
# Rebuild it using:
# $ oak_containers/system_image/build-base.sh sysroot
#
# Upload it using:
# $ oak_containers/system_image/push-base.sh sysroot
#
# (See oak_containers/system_image/README.md for more details.)
http_archive(
    name = "oak_cc_toolchain_sysroot",
    build_file = "//:toolchain/sysroot.BUILD",
    sha256 = SYSROOT_SHA256,
    url = "https://storage.googleapis.com/oak-bins/sysroot/" + SYSROOT_SHA256 + ".tar.xz",
)

# The binary is used for stage0 tdx measurement test
# (//tdx_measurement:tdx_measurement_test) only.
STAGE0_BIN_TDX_COMMIT = "0689771e6fd6d174121eaa0b7df5fe54c4746ce3"

http_file(
    name = "stage0_tdx_bin_for_test",
    downloaded_file_path = "stage0_tdx_bin_for_test",
    sha256 = "87fe23ad59066718f97acfe2672f70e6ddfa488f7593d59b8886f67d0ca08715",
    url = "https://storage.googleapis.com/oak-bins/binary/" + STAGE0_BIN_TDX_COMMIT + "/stage0_bin_tdx/binary",
)

http_file(
    name = "oak_containers_system_image_base",
    downloaded_file_path = "base-image.tar.xz",
    sha256 = BASE_IMAGE_SHA256,
    url = "https://storage.googleapis.com/oak-bins/base-image/" + BASE_IMAGE_SHA256 + ".tar.xz",
)

http_file(
    name = "oak_containers_nvidia_system_image_base",
    downloaded_file_path = "nvidia-base-image.tar.xz",
    sha256 = NVIDIA_BASE_IMAGE_SHA256,
    url = "https://storage.googleapis.com/oak-bins/nvidia-base-image/" + NVIDIA_BASE_IMAGE_SHA256 + ".tar.xz",
)

load("//bazel/llvm:deps.bzl", "load_llvm_repositories")

load_llvm_repositories()

load("//bazel/llvm:defs.bzl", "setup_llvm_toolchains")

setup_llvm_toolchains()

load("//bazel/llvm:reg.bzl", "register_llvm_toolchains")

register_llvm_toolchains()

load("//bazel/rust:deps.bzl", "load_rust_repositories")

load_rust_repositories()

load("//bazel/rust:defs.bzl", "setup_rust_dependencies")

setup_rust_dependencies()

load("//bazel/rust:stdlibs.bzl", "setup_rebuilt_rust_stdlibs")

setup_rebuilt_rust_stdlibs()

load("//bazel/crates:repositories.bzl", "create_oak_crate_repositories")

create_oak_crate_repositories()

load("//bazel/crates:crates.bzl", "load_oak_crate_repositories")

load_oak_crate_repositories()

http_archive(
    name = "e2fsprogs",
    build_file = "@//:third_party/BUILD.e2fsprogs",
    sha256 = "144af53f2bbd921cef6f8bea88bb9faddca865da3fbc657cc9b4d2001097d5db",
    strip_prefix = "e2fsprogs-1.47.0",
    urls = ["https://mirrors.edge.kernel.org/pub/linux/kernel/people/tytso/e2fsprogs/v1.47.0/e2fsprogs-1.47.0.tar.xz"],
)

load("//bazel/nix:kernel.bzl", "nix_kernel_repo")

# Get the nix-built Kernels into our Bazel workspace, and verify the sha256
nix_kernel_repo(
    name = "nix_kernels",
    bzImage_sha256 = "9e4dd5c5cebb4be3bea8747035979ab373b92124bbb9dcdef19325cea7116717",
    bzImage_vanilla_sha256 = "1ce6de1a2c4885dbf6d445a5bac390e285a76104d52e5356501330b409aaf141",
)

http_archive(
    name = "rules_rust_wasm_bindgen",
    integrity = "sha256-U8G6x+xI985IxMHGqgBvJ1Fa3SrrBXJZNyJObgDsfOo=",
    strip_prefix = "extensions/wasm_bindgen",
    urls = ["https://github.com/bazelbuild/rules_rust/releases/download/0.61.0/rules_rust-0.61.0.tar.gz"],
)

load("@rules_rust_wasm_bindgen//:repositories.bzl", "rust_wasm_bindgen_dependencies", "rust_wasm_bindgen_register_toolchains")

rust_wasm_bindgen_dependencies()

rust_wasm_bindgen_register_toolchains()
