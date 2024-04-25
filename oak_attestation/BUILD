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
load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_attestation",
    srcs = glob(["src/**"]),
    deps = [
        ":build",
        "//micro_rpc",
        "//oak_crypto",
        "//oak_dice",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:ciborium",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:log",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:zeroize",
    ],
)

cargo_build_script(
    name = "build",
    srcs = [
        "build.rs",
    ],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
    },
    data = [
        "//proto/attestation:dice_proto",
        "//proto/attestation:endorsement_proto",
        "//proto/attestation:evidence_proto",
        "//proto/session:messages_proto",
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//micro_rpc_build",
        "@oak_crates_index//:prost-build",
    ],
)
