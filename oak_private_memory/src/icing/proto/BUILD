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

load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
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
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:well_known_type_protos",
        "@icing//:icing_proto_srcs",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "@oak//oak_grpc_utils",
        "@oak//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:walkdir",
        "@rules_rust//tools/runfiles",
    ],
)

rust_library(
    name = "icing_rust_proto",
    srcs = ["lib.rs"],
    proc_macro_deps = [
        "@oak_crates_index//:prost-derive",
    ],
    deps = [
        ":build",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde-aux",
        "@oak_crates_index//:tonic",
    ],
)
