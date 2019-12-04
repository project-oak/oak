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
    sha256 = "7f53d61d91a8d6963a5665088b02129d643a4cfbcab883f1076b71bcbe07184d",
    strip_prefix = "asylo-088ea3490dd4579655bd5b65b0e31fe18de7f6dd",
    urls = [
        # Head commit on 2019-11-21.
        "https://github.com/google/asylo/archive/088ea3490dd4579655bd5b65b0e31fe18de7f6dd.tar.gz",
    ],
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

# WebAssembly Binary Toolkit
http_archive(
    name = "wabt",
    build_file = "@//third_party/wabt:wabt.BUILD",
    patches = [
        "//third_party/wabt:0003-Add-static-config-file.patch",
        "//third_party/wabt:0007-Include-opcode-code-table.c.patch",
        "//third_party/wabt:0010-Use-std-stringstream-to-build-unique-name.patch",
    ],
    sha256 = "8bf8123b93c627bbd762fa54ec2e968db73a5155e9a5ae32c722b05350be4a21",
    strip_prefix = "wabt-39ceee53a9cd23451a28d4e56e151ef76044b5df",
    urls = ["https://github.com/WebAssembly/wabt/archive/39ceee53a9cd23451a28d4e56e151ef76044b5df.tar.gz"],
)

# Tool used for creating a compilation database.
http_archive(
    name = "io_kythe",
    sha256 = "85dac12cdeea46f9e369ff109934aa98967bed1cd7c4c4afdc11577c3f99d31a",
    strip_prefix = "kythe-4814f9f3fcc05c49fbe11f62f1e58a428048da27",
    urls = [
        # Head commit on 2019-12-03.
        "https://github.com/kythe/kythe/archive/4814f9f3fcc05c49fbe11f62f1e58a428048da27.tar.gz"
    ],
)

# Kythe tool dependency.
# Loading only a subset of Kythe dependencies necessary for
# compilation database generation.
# https://github.com/kythe/kythe/blob/4814f9f3fcc05c49fbe11f62f1e58a428048da27/external.bzl#L110-L123
http_archive(
    name = "com_github_google_glog",
    strip_prefix = "glog-ba8a9f6952d04d1403b97df24e6836227751454e",
    sha256 = "9b4867ab66c33c41e2672b5de7e3133d38411cdb75eeb0d2b72c88bb10375c71",
    url = "https://github.com/google/glog/archive/ba8a9f6952d04d1403b97df24e6836227751454e.zip",
    build_file_content = "\n".join([
            "load(\"//:bazel/glog.bzl\", \"glog_library\")",
            "glog_library(with_gflags=0)",
        ]),
)

# Kythe tool dependency.
# https://github.com/kythe/kythe/blob/4814f9f3fcc05c49fbe11f62f1e58a428048da27/external.bzl#L75-L85
http_archive(
    name = "com_github_tencent_rapidjson",
    sha256 = "8e00c38829d6785a2dfb951bb87c6974fa07dfe488aa5b25deec4b8bc0f6a3ab",
    strip_prefix = "rapidjson-1.1.0",
    url = "https://github.com/Tencent/rapidjson/archive/v1.1.0.zip",
    build_file = "@io_kythe//third_party:rapidjson.BUILD",
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

load("@io_kythe//:setup.bzl", "kythe_rule_repositories")

kythe_rule_repositories()

load("@io_bazel_rules_go//go/private:compat/compat_repo.bzl", "go_rules_compat")
go_rules_compat(
    name = "io_bazel_rules_go_compat"
)

# clang + llvm 8.0
http_archive(
    name = "clang",
    build_file = "//toolchain:clang.BUILD",
    sha256 = "0f5c314f375ebd5c35b8c1d5e5b161d9efaeff0523bac287f8b4e5b751272f51",
    strip_prefix = "clang+llvm-8.0.0-x86_64-linux-gnu-ubuntu-18.04",
    url = "http://releases.llvm.org/8.0.0/clang+llvm-8.0.0-x86_64-linux-gnu-ubuntu-18.04.tar.xz",
)
