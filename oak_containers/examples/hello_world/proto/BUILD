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
load("@com_google_protobuf//bazel:proto_library.bzl", "proto_library")
load("//oak_grpc_utils:build_defs.bzl", "rust_tonic_grpc_service")

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

rust_tonic_grpc_service(
    name = "hello_world_rust_proto",
    srcs = [":hello_world_proto"],
    crate_name = "oak_hello_world_proto",
    extern_paths = {
        ".oak": "::oak_proto_rust::oak",
    },
    deps = [
        "//oak_proto_rust",
    ],
)
