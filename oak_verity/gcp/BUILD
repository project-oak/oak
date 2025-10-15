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
    name = "oak_verity_gcp",
    srcs = ["main.rs"],
    deps = [
        "//oak_attestation_gcp",
        "//oak_attestation_types",
        "//oak_proto_rust/grpc",
        "//oak_verity/grpc:oak_verity_grpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:maplit",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)
