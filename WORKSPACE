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
    sha256 = "cd4dd948bfe3655269656277eb83dbeefcb1368d7c6b329e93cc8ca9a688e5e6",
    strip_prefix = "abseil-cpp-27c30ec671cb7b5ba84c4e79feff7fd0b0ac6338",
    urls = [
        # Head commit on 2019-05-23.
        "https://github.com/abseil/abseil-cpp/archive/27c30ec671cb7b5ba84c4e79feff7fd0b0ac6338.zip",
    ],
)

# Asylo Framework.
http_archive(
    name = "com_google_asylo",
    sha256 = "b622044f967da3b8a8e2c76a18afe0014baab3226a902db0b87255f3ffc31c2c",
    strip_prefix = "asylo-dfdc44744e3b18531830deb37c5633f648e6cdbd",
    urls = ["https://github.com/google/asylo/archive/dfdc44744e3b18531830deb37c5633f648e6cdbd.tar.gz"],
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
    commit = "910d762920ac7575d7e3e04791a9d9c0ae07f8cd",
    remote = "https://github.com/daviddrysdale/wabt",
)

load(
    "@com_google_asylo//asylo/bazel:asylo_deps.bzl",
    "asylo_deps",
    "asylo_go_deps",
)

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
