#
# Copyright 2024 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")
load("@rules_shell//shell:sh_binary.bzl", "sh_binary")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "lib",
    srcs = [
        "src/lib.rs",
        "src/qemu.rs",
        "src/server.rs",
    ],
    crate_name = "oak_containers_launcher",
    deps = [
        "//oak_launcher_utils",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:command-fds",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:log",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:opentelemetry-proto",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tokio-vsock",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:which",
    ],
)

rust_binary(
    name = "oak_containers_launcher",
    srcs = ["src/main.rs"],
    deps = [
        ":lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:tokio",
    ],
)

alias(
    name = "launcher",
    actual = ":oak_containers_launcher",
)

sh_binary(
    name = "nswrap",
    srcs = ["nswrap.sh"],
)
