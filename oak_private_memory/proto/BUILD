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

load("@rules_proto//proto:defs.bzl", "proto_library")
load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "sealed_memory_proto",
    srcs = [
        "database.proto",
        "internal.proto",
        "sealed_memory.proto",
    ],
    deps = [
        "@oak//proto/session:session_proto",
    ],
)

cargo_build_script(
    name = "build",
    srcs = [
        "build.rs",
    ],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
        "DESCRIPTOR_PROTO_PATH": "$(location @com_google_protobuf//:descriptor_proto_srcs)",
        "OAK_PROTO_PATH": "$(location @oak//proto/session:session.proto)",
    },
    data = [
        ":database.proto",
        ":internal.proto",
        ":sealed_memory.proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:well_known_type_protos",
        "@oak//proto:digest.proto",
        "@oak//proto:variant.proto",
        "@oak//proto/attestation:endorsement.proto",
        "@oak//proto/attestation:eventlog.proto",
        "@oak//proto/attestation:evidence.proto",
        "@oak//proto/crypto:certificate.proto",
        "@oak//proto/crypto:crypto.proto",
        "@oak//proto/session:messages.proto",
        "@oak//proto/session:service_streaming.proto",
        "@oak//proto/session:session.proto",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "@oak//oak_grpc_utils",
        "@oak//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
        "@oak_crates_index//:serde",
    ],
)

rust_library(
    name = "sealed_memory_rust_proto",
    srcs = [
        "lib.rs",
        "prelude.rs",
    ],
    proc_macro_deps = [
        "@oak_crates_index//:prost-derive",
    ],
    deps = [
        ":build",
        "@oak//oak_proto_rust",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde-aux",
        "@oak_crates_index//:tonic",
    ],
)
