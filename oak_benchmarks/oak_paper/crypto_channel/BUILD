#
# Copyright 2026 The Project Oak Authors
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

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "message_stream",
    srcs = ["message_stream.rs"],
    deps = [
        "//oak_channel",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:prost",
    ],
)

rust_library(
    name = "message_stream_client",
    srcs = ["message_stream.rs"],
    deps = [
        "//oak_channel:oak_channel_client",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:prost",
    ],
)

rust_binary(
    name = "benchmark",
    srcs = [
        "benchmark.rs",
    ],
    crate_root = "benchmark.rs",
    data = [
        ":enclave_app",
        "//enclave_apps/oak_orchestrator",
        "//oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin",
        "//stage0_bin",
    ],
    env = {
        "RUST_LOG": "debug",
        "RUST_BACKTRACE": "1",
    },
    deps = [
        ":message_stream_client",
        "//oak_channel:oak_channel_client",
        "//oak_file_utils",
        "//oak_launcher_utils",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:criterion",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:which",
    ],
)

rust_binary(
    name = "enclave_app",
    srcs = ["enclave_app.rs"],
    platform = "//:x86_64-unknown-none",
    rustc_flags = [
        "--codegen=link-arg=-Wl,-zmax-page-size=0x200000",
    ],
    deps = [
        ":message_stream",
        "//oak_channel",
        "//oak_restricted_kernel_sdk",
        "@oak_crates_index//:log",
    ],
)
