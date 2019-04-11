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

# Asylo Framework v0.3.4.1
http_archive(
    name = "com_google_asylo",
    urls = ["https://github.com/google/asylo/archive/v0.3.4.1.tar.gz"],
    strip_prefix = "asylo-0.3.4.1",
    sha256 = "5001ff28b03b9a604d77b393deedfa75ed7c553cd7d75332fe52ef147bedbbba",
)

# Google Protocol Buffers v3.6.1.2
http_archive(
    name = "com_google_protobuf",
    urls = [
        "https://github.com/protocolbuffers/protobuf/archive/v3.6.1.2.tar.gz",
    ],
    strip_prefix = "protobuf-3.6.1.2",
    sha256 = "2244b0308846bb22b4ff0bcc675e99290ff9f1115553ae9671eba1030af31bc0",
)

# WebAssembly Binary Toolkit (forked by tiziano88)
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
