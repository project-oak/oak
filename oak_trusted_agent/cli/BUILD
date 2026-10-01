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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_binary(
    name = "oak_trusted_agent_cli",
    srcs = ["src/main.rs"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_test(
    name = "cli_test",
    size = "small",
    srcs = ["tests/cli_test.rs"],
    data = [
        ":oak_trusted_agent_cli",
        "//oak_trusted_agent/sandbox/guest/agent_ts:adk_agent_ts",
    ],
    rustc_env = {
        "ADK_AGENT_TS_WASM": "$(rootpath //oak_trusted_agent/sandbox/guest/agent_ts:adk_agent_ts)",
        "OAK_TRUSTED_AGENT_CLI": "$(rootpath :oak_trusted_agent_cli)",
    },
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//oak_proto_rust/grpc",
        "//oak_trusted_agent/sandbox/host",
        "//oak_trusted_agent/server",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)
