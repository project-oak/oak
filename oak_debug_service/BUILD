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
    name = "oak_debug_service",
    srcs = glob(["src/**"]),
    deps = [
        ":build",
        "@oak_crates_index//:pprof",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
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
        # Needed by `oak_proto_build_utils::get_common_proto_path`
        "DESCRIPTOR_PROTO_PATH": "$(location @com_google_protobuf//:descriptor_proto_srcs)",
    },
    crate_features = ["bazel"],
    data = [
        "//proto/oak_debug/service:oak_debug_proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
        "@com_google_protobuf//:duration_proto",
        "@com_google_protobuf//:protoc",
        "@com_google_protobuf//:well_known_type_protos",
    ],
    deps = [
        "//oak_grpc_utils",
        "//oak_proto_build_utils",
    ],
)
