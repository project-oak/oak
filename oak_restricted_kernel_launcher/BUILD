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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "main",
    srcs = ["src/main.rs"],
    deps = [
        ":lib",
        "//oak_launcher_utils",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
    ],
)

rust_library(
    name = "lib",
    srcs = ["src/lib.rs"],
    crate_name = "oak_restricted_kernel_launcher",
    deps = [
        "//oak_launcher_utils",
        "@oak_crates_index//:log",
    ],
)

rust_test(
    name = "tests",
    srcs = ["src/tests.rs"],
    data = [
        "//enclave_apps/oak_echo_enclave_app",
        "//enclave_apps/oak_orchestrator",
        "//oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin",
        "//stage0_bin",
    ],
    deps = [
        ":lib",
        "//micro_rpc",
        "//oak_file_utils",
        "//oak_launcher_utils",
        "//oak_proto_rust/micro_rpc",
        "//testing/oak_echo_service",
        "//testing/oak_echo_service/proto:service",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:ubyte",
        "@oak_crates_index//:which",
    ],
)
