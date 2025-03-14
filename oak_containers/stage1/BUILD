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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_containers_stage1",
    srcs = glob(["src/**"]),
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_containers/attestation",
        "//oak_containers/channel",
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:futures-util",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rtnetlink",
        "@oak_crates_index//:tar",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:xz2",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)

alias(
    name = "stage1",
    actual = ":oak_containers_stage1",
)

rust_test(
    name = "oak_containers_stage1_tests",
    crate = ":oak_containers_stage1",
)
