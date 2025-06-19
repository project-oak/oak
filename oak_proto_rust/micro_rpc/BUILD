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
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "micro_rpc",
    srcs = [
        "lib.rs",
    ],
    crate_name = "oak_micro_rpc",
    deps = [
        ":build",
        "//micro_rpc",
        "//oak_proto_rust",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
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
        "//proto/attestation:eventlog.proto",
        "//proto/attestation:evidence.proto",
        "//proto/crypto:crypto.proto",
        "//proto/micro_rpc:options.proto",
        "//proto/oak_functions:testing.proto",
        "//proto/oak_functions/sdk:oak_functions_wasm.proto",
        "//proto/oak_functions/service:oak_functions.proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:well_known_type_protos",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//micro_rpc_build",
        "//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
    ],
)
