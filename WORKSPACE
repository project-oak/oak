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

http_archive(
    name = "com_google_asylo",
    urls = ["https://github.com/google/asylo/archive/v0.3.2.tar.gz"],
    strip_prefix = "asylo-0.3.2",
    sha256 = "4af6fcc16b7dc1ba8cccdce9086859e66f180f042b946abd8a45ed76dd330016",
)

load(
    "@com_google_asylo//asylo/bazel:asylo_deps.bzl",
    "asylo_deps",
    "asylo_go_deps",
)
asylo_deps()
asylo_go_deps()

load(
    "@com_google_asylo//asylo/bazel:sgx_deps.bzl",
    "sgx_deps",
)
sgx_deps()

load(
    "@com_github_grpc_grpc//bazel:grpc_deps.bzl",
    "grpc_deps",
)
grpc_deps()

load("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")

git_repository(
    name = "wabt",
    commit = "2d31cda394fc67c7969a9bd44066cb8eafa82e23",
    remote = "https://github.com/tiziano88/wabt",
)
