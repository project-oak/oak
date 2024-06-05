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
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "lib",
    srcs = [
        "src/container_runtime.rs",
        "src/crypto.rs",
        "src/dice.rs",
        "src/ipc_server.rs",
        "src/key_provisioning.rs",
        "src/launcher_client.rs",
        "src/lib.rs",
        "src/logging.rs",
    ],
    crate_features = ["bazel"],
    crate_name = "oak_containers_orchestrator",
    deps = [
        ":build",
        "//oak_attestation",
        "//oak_attestation_verification",
        "//oak_crypto",
        "//oak_dice",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:ciborium",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:hpke",
        "@oak_crates_index//:log",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:oci-spec",
        "@oak_crates_index//:opentelemetry",
        "@oak_crates_index//:opentelemetry-otlp",
        "@oak_crates_index//:opentelemetry_sdk",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:procfs",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:syslog",
        "@oak_crates_index//:tar",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tokio-util",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:walkdir",
        "@oak_crates_index//:zeroize",
    ],
)

rust_binary(
    name = "oak_containers_orchestrator",
    srcs = ["src/main.rs"],
    deps = [
        ":lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:nix",
        "@oak_crates_index//:tikv-jemallocator",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-util",
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
    crate_features = ["bazel"],
    data = [
        "//proto/containers:hostlib_key_provisioning_proto",
        "//proto/containers:interfaces_proto",
        "//proto/containers:orchestrator_crypto_proto",
        "//proto/key_provisioning:key_provisioning_proto",
        "//proto/session:messages_proto",
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//oak_grpc_utils",
        "@oak_crates_index//:prost-build",
    ],
)
