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
load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

http_archive(
    name = "com_google_absl",
    sha256 = "27184e97131edb9a289b1c2cd404c234afa5ceaae44c5eb6713138cb674535aa",
    strip_prefix = "abseil-cpp-ac78ffc3bc0a8b295cab9a03817760fd460df2a1",
    urls = [
        # Head commit on 2019-09-12.
        "https://github.com/abseil/abseil-cpp/archive/ac78ffc3bc0a8b295cab9a03817760fd460df2a1.zip",
    ],
)

# Asylo Framework.
http_archive(
    name = "com_google_asylo",
    sha256 = "a15b5b436d27b3fd426de2f3d8598264f7ccf8a79421b5cfd41b95c832e3e9b0",
    strip_prefix = "asylo-361737de928acbd01a6ca206292bf79c0484c62b",
    urls = ["https://github.com/google/asylo/archive/361737de928acbd01a6ca206292bf79c0484c62b.tar.gz"],
)

# Google Test
git_repository(
    name = "gtest",
    commit = "2fe3bd994b3189899d93f1d5a881e725e046fdc2",
    remote = "https://github.com/google/googletest",
)

# Google Protocol Buffers.
http_archive(
    name = "com_google_protobuf",
    sha256 = "98e615d592d237f94db8bf033fba78cd404d979b0b70351a9e5aaff725398357",
    strip_prefix = "protobuf-3.9.1",
    urls = [
        "https://github.com/protocolbuffers/protobuf/archive/v3.9.1.tar.gz",
    ],
)

load("@com_google_protobuf//:protobuf_deps.bzl", "protobuf_deps")

protobuf_deps()

# Google APIs for Cloud Spanner protos.
# TODO: Switch from fork after https://github.com/googleapis/googleapis/pull/553 is merged.
http_archive(
    name = "com_google_googleapis",
    sha256 = "3a426981242af9c05dbc3cdfc72f6627516232bbccaebaab1711397606184973",
    strip_prefix = "googleapis-66d43496b46c26915d7d37302cddbd81481302d7",
    urls = [
        "https://github.com/michael-kernel-sanders/googleapis/archive/66d43496b46c26915d7d37302cddbd81481302d7.zip",
    ],
)

# TODO: Create a deps function for the googleapis repo.
http_archive(
    name = "io_grpc_grpc_java",
    sha256 = "9d23d9fec84e24bd3962f5ef9d1fd61ce939d3f649a22bcab0f19e8167fae8ef",
    strip_prefix = "grpc-java-1.20.0",
    urls = [
        "https://github.com/grpc/grpc-java/archive/v1.20.0.zip",
    ],
)

# TODO: Create a deps function for the googleapis repo.
http_archive(
    name = "com_google_api_codegen",
    sha256 = "ba19948ebc4ea39358ba07fc0253f8927d7a2c9ba3462e8f34faad7ad5ac4142",
    strip_prefix = "gapic-generator-8e930b79e846b9d4876462be9dc4c1dbc04e2903",
    urls = ["https://github.com/googleapis/gapic-generator/archive/8e930b79e846b9d4876462be9dc4c1dbc04e2903.zip"],
)

# WebAssembly Binary Toolkit (forked by tiziano88).
git_repository(
    name = "wabt",
    commit = "30e914b1630db13080cc054b591ab5822b9b4768",
    remote = "https://github.com/daviddrysdale/wabt",
)

http_archive(
    name = "bazel_skylib",
    sha256 = "9a737999532daca978a158f94e77e9af6a6a169709c0cee274f0a4c3359519bd",
    strip_prefix = "bazel-skylib-1.0.0",
    url = "https://github.com/bazelbuild/bazel-skylib/archive/1.0.0.tar.gz",
)

http_archive(
    name = "io_bazel_rules_rust",
    repo_mapping = {"@bazel_version": "@bazel_version_rust"},
    sha256 = "69b67e19532b12da3edccda404772e85a788d16ae739343f5338dd340a0fba2e",
    strip_prefix = "rules_rust-ec436b5ff2ab1ddeba6f27a7a1a5d263812981a6",
    urls = [
        # Master branch as of 2019-11-15.
        "https://github.com/bazelbuild/rules_rust/archive/ec436b5ff2ab1ddeba6f27a7a1a5d263812981a6.tar.gz",
    ],
)

load("@io_bazel_rules_rust//rust:repositories.bzl", "rust_repository_set")

rust_repository_set(
    name = "rust_linux_x86_64",
    exec_triple = "x86_64-unknown-linux-gnu",
    extra_target_triples = [],
    iso_date = "2019-11-06",
    version = "nightly",
)

load("@io_bazel_rules_rust//:workspace.bzl", "bazel_version")

# We need to alias this with a different name so it does not conflict with an existing rule imported
# from Asylo.
# See https://github.com/google/asylo/issues/44.
bazel_version(name = "bazel_version_rust")

load("@com_google_asylo//asylo/bazel:asylo_deps.bzl", "asylo_deps", "asylo_go_deps")

asylo_deps()

asylo_go_deps()

load("@com_google_asylo//asylo/bazel:sgx_deps.bzl", "sgx_deps")

sgx_deps()

load("@com_github_grpc_grpc//bazel:grpc_deps.bzl", "grpc_deps")

grpc_deps()

# clang + llvm 8.0
http_archive(
    name = "clang",
    build_file = "//toolchain:clang.BUILD",
    sha256 = "0f5c314f375ebd5c35b8c1d5e5b161d9efaeff0523bac287f8b4e5b751272f51",
    strip_prefix = "clang+llvm-8.0.0-x86_64-linux-gnu-ubuntu-18.04",
    url = "http://releases.llvm.org/8.0.0/clang+llvm-8.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz",
)
