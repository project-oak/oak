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
    urls = [
         # Head commit on 2019-05-23.
         "https://github.com/abseil/abseil-cpp/archive/27c30ec671cb7b5ba84c4e79feff7fd0b0ac6338.zip"],
    strip_prefix = "abseil-cpp-27c30ec671cb7b5ba84c4e79feff7fd0b0ac6338",
    sha256 = "cd4dd948bfe3655269656277eb83dbeefcb1368d7c6b329e93cc8ca9a688e5e6",
)

# Asylo Framework.
http_archive(
    name = "com_google_asylo",
    urls = ["https://github.com/google/asylo/archive/v0.3.4.2.tar.gz"],
    strip_prefix = "asylo-0.3.4.2",
    sha256 = "82226be212b9f3e2fb14fdf9223e4f376df89424874ac45faff215fa1027797e",
)

# Google Protocol Buffers.
http_archive(
    name = "com_google_protobuf",
    urls = [
        "https://github.com/protocolbuffers/protobuf/archive/v3.8.0.tar.gz",
    ],
    strip_prefix = "protobuf-3.8.0",
    sha256 = "03d2e5ef101aee4c2f6ddcf145d2a04926b9c19e7086944df3842b1b8502b783",
)

load(
    "@com_google_protobuf//:protobuf_deps.bzl",
    "protobuf_deps"
)
protobuf_deps()

# gRPC
# TODO: Remove after Asylo upgrades for 0803c79411597f58eae0b12b4eb272c506b8cdbb.
load(
    "@com_google_asylo//asylo/bazel:patch_repository.bzl",
    "patch_repository",
)
patch_repository(
    name = "com_github_grpc_grpc",
    urls = [
        "https://github.com/grpc/grpc/archive/cb9b43b9f7291ceb714d92e0a717c6364c1fcc61.zip",
    ],
    patches = ["@com_google_asylo//asylo/distrib:grpc_1_19_1.patch"],
    strip_prefix = "grpc-cb9b43b9f7291ceb714d92e0a717c6364c1fcc61",
    sha256 = "8492eae54b2032c5993bd720c9ffe6ea4b05b9bdeb33534453b7129bd98d500a",
)

# Google APIs for Cloud Spanner protos.
# TODO: Switch from fork after https://github.com/googleapis/googleapis/pull/553 is merged.
http_archive(
    name = "com_google_googleapis",
    urls = [
        "https://github.com/michael-kernel-sanders/googleapis/archive/66d43496b46c26915d7d37302cddbd81481302d7.zip"
    ],
    strip_prefix = "googleapis-66d43496b46c26915d7d37302cddbd81481302d7",
    sha256 = "3a426981242af9c05dbc3cdfc72f6627516232bbccaebaab1711397606184973",
)

# TODO: Create a deps function for the googleapis repo.
http_archive(
    name = "io_grpc_grpc_java",
    urls = [
        "https://github.com/grpc/grpc-java/archive/v1.20.0.zip",
    ],
    strip_prefix = "grpc-java-1.20.0",
    sha256 = "9d23d9fec84e24bd3962f5ef9d1fd61ce939d3f649a22bcab0f19e8167fae8ef",
)

# TODO: Create a deps function for the googleapis repo.
http_archive(
    name = "com_google_api_codegen",
    urls = ["https://github.com/googleapis/gapic-generator/archive/8e930b79e846b9d4876462be9dc4c1dbc04e2903.zip"],
    strip_prefix = "gapic-generator-8e930b79e846b9d4876462be9dc4c1dbc04e2903",
    sha256 = "ba19948ebc4ea39358ba07fc0253f8927d7a2c9ba3462e8f34faad7ad5ac4142",
)

# WebAssembly Binary Toolkit (forked by tiziano88).
git_repository(
    name = "wabt",
    commit = "2d31cda394fc67c7969a9bd44066cb8eafa82e23",
    remote = "https://github.com/tiziano88/wabt",
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

