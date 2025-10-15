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
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "grpc",
    srcs = [
        "lib.rs",
    ],
    crate_name = "oak_grpc",
    deps = [
        ":build",
        "//oak_proto_rust",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tonic",
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
    },
    data = [
        "//proto:digest.proto",
        "//proto:validity.proto",
        "//proto:variant.proto",
        "//proto/attestation:assertion.proto",
        "//proto/attestation:endorsement.proto",
        "//proto/attestation:eventlog.proto",
        "//proto/attestation:evidence.proto",
        "//proto/containers:hostlib_key_provisioning.proto",
        "//proto/containers:interfaces.proto",
        "//proto/containers:orchestrator_crypto.proto",
        "//proto/crypto:certificate.proto",
        "//proto/crypto:crypto.proto",
        "//proto/key_provisioning:key_provisioning.proto",
        "//proto/micro_rpc:options.proto",
        "//proto/oak_debug/service:oak_debug.proto",
        "//proto/oak_functions/service:oak_functions.proto",
        "//proto/oak_functions/standalone:oak_functions_session.proto",
        "//proto/oak_verity:oak_verity.proto",
        "//proto/session:messages.proto",
        "//proto/session:service_streaming.proto",
        "//proto/session:session.proto",
        "//third_party/google:profile.proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:protoc",
        "@com_google_protobuf//:well_known_type_protos",
    ],
    deps = [
        "//oak_grpc_utils",
        "//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
    ],
)
