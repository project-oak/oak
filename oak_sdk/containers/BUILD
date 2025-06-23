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

load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_sdk_containers",
    srcs = ["lib.rs"],
    deps = [
        ":orchestrator_channel",
        ":orchestrator_client",
        ":orchestrator_crypto_client",
        "//oak_containers/agent:oak_containers_agent",
    ],
)

rust_library(
    name = "orchestrator_channel",
    srcs = ["orchestrator_channel.rs"],
    visibility = ["//oak_sdk:__subpackages__"],
    deps = [
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:hyper-util",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:tower",
    ],
)

rust_library(
    name = "orchestrator_crypto_client",
    srcs = ["orchestrator_crypto_client.rs"],
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    visibility = ["//oak_sdk:__subpackages__"],
    deps = [
        "//oak_crypto",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

rust_library(
    name = "orchestrator_client",
    srcs = ["orchestrator_client.rs"],
    visibility = ["//oak_sdk:__subpackages__"],
    deps = [
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:tonic",
    ],
)
