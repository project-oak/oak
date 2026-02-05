#
# Copyright 2026 The Project Oak Authors
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

load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")
load("@rules_rust//cargo:defs.bzl", "cargo_build_script")
load("@rules_rust//rust:defs.bzl", "rust_library")
load("//micro_rpc_build:build_defs.bzl", "rust_micro_rpc_service")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

proto_library(
    name = "proto",
    srcs = ["benchmark.proto"],
    deps = [
        "//proto/micro_rpc:options_proto",
    ],
)

rust_library(
    name = "oak_benchmark_proto_rust",
    srcs = ["lib.rs"],
    proc_macro_deps = [
        "@oak_crates_index//:prost-derive",
    ],
    deps = [
        ":build",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
    ],
)

cargo_build_script(
    name = "build",
    srcs = ["build.rs"],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
        "DESCRIPTOR_PROTO_PATH": "$(location @com_google_protobuf//:descriptor_proto_srcs)",
    },
    data = [
        "benchmark.proto",
        "//proto/micro_rpc:options.proto",
        "@com_google_protobuf//:descriptor_proto_srcs",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
    ],
)

rust_micro_rpc_service(
    name = "service",
    srcs = [":proto"],
    extern_paths = {
        ".oak.benchmark": ":oak_benchmark_proto_rust::oak::benchmark",
    },
    deps = [":oak_benchmark_proto_rust"],
)
