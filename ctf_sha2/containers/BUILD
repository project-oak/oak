#
# Copyright 2025 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//oak_containers/app_base:defs.bzl", "app_bundle")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "enclave_app",
    srcs = ["enclave_app.rs"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//ctf_sha2/containers/proto:tonic_service",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_sdk/containers:oak_sdk_containers",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:rand",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

app_bundle(
    name = "bundle",
    binary = ":enclave_app",
    target_compatible_with = ["@platforms//os:linux"],
)

rust_binary(
    name = "host_app",
    srcs = ["host_app.rs"],
    data = [
        ":bundle",
        "//oak_containers/kernel:bzImage",
        "//oak_containers/stage1_bin:stage1_cpio",
        "//oak_containers/system_image:oak_containers_system_image",
        "//stage0_bin",
    ],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//ctf_sha2/containers/proto:tonic_service",
        "//oak_containers/launcher:lib",
        "//oak_file_utils",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:which",
    ],
)
