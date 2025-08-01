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

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_binary(
    name = "mcp_server",
    srcs = glob([
        "src/*.rs",
    ]),
    deps = [
        "//oak_functions_standalone/client:oak_functions_standalone_client_lib",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_session",
        "//oak_time",
        "//oak_time:oak_time_std",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rmcp",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)
