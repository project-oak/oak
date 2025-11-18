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

load("@rules_proto//proto:defs.bzl", "proto_library")
load("//oak_grpc_utils:build_defs.bzl", "rust_tonic_grpc_service")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

proto_library(
    name = "echo_proto",
    srcs = ["echo.proto"],
    deps = [
        "//proto/session:session_proto",
    ],
)

rust_tonic_grpc_service(
    name = "echo_rust_proto",
    srcs = [":echo_proto"],
    crate_name = "oak_gcp_echo_proto",
    extern_paths = {
        ".oak": "::oak_proto_rust::oak",
    },
    deps = [
        "//oak_proto_rust",
    ],
)
