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
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_containers_sdk",
    srcs = [
        "src/attestation.rs",
        "src/crypto.rs",
        "src/handler.rs",
        "src/lib.rs",
        "src/oak_session_context.rs",
        "src/orchestrator_client.rs",
        "src/standalone.rs",
        "src/tonic.rs",
    ],
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//oak_attestation",
        "//oak_containers/oak_containers_orchestrator_attestation",
        "//oak_containers/stage1_dice",
        "//oak_crypto",
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_session",
        "//stage0_dice",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:tower",
    ],
)
