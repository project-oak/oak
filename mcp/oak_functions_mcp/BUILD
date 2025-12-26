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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_functions_mcp_lib",
    srcs = glob(["src/*.rs"]),
    proc_macro_deps = [
        "@oak_std_crates_index//:rmcp-macros",
        "@oak_std_crates_index//:async-trait",
    ],
    deps = [
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:axum",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:rmcp",
        "@oak_crates_index//:tokio",
    ],
)

rust_binary(
    name = "oak_functions_mcp_server",
    srcs = ["src/main.rs"],
    deps = [
        ":oak_functions_mcp_lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:axum",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:rmcp",
        "@oak_crates_index//:tokio",
    ],
)
