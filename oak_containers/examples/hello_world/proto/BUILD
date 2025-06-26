#
# Copyright 2023 The Project Oak Authors
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

load("@com_github_grpc_grpc//bazel:cc_grpc_library.bzl", "cc_grpc_library")
load("@com_google_protobuf//bazel:cc_proto_library.bzl", "cc_proto_library")
load("@rules_proto//proto:defs.bzl", "proto_library")
load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

proto_library(
    name = "hello_world_proto",
    srcs = ["hello_world.proto"],
    deps = [
        "//proto/session:service_streaming_proto",
        "//proto/session:session_proto",
    ],
)

cc_proto_library(
    name = "hello_world_cc_proto",
    deps = [":hello_world_proto"],
)

cc_grpc_library(
    name = "hello_world_cc_grpc",
    srcs = [":hello_world_proto"],
    grpc_only = True,
    deps = [":hello_world_cc_proto"],
)

cargo_build_script(
    name = "build",
    srcs = [
        "build.rs",
    ],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
        "DESCRIPTOR_PROTO_PATH": "$(location @com_google_protobuf//:descriptor_proto_srcs)",
    },
    data = [
        ":hello_world.proto",
        "//proto:digest.proto",
        "//proto:validity.proto",
        "//proto:variant.proto",
        "//proto/attestation:endorsement.proto",
        "//proto/attestation:eventlog.proto",
        "//proto/attestation:evidence.proto",
        "//proto/crypto:certificate.proto",
        "//proto/crypto:crypto.proto",
        "//proto/session:messages.proto",
        "//proto/session:service_streaming.proto",
        "//proto/session:session.proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:well_known_type_protos",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//oak_grpc_utils",
        "//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
    ],
)

rust_library(
    name = "hello_world_rust_proto",
    srcs = ["lib.rs"],
    crate_name = "oak_hello_world_proto",
    deps = [
        ":build",
        "//oak_proto_rust",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tonic",
    ],
)
