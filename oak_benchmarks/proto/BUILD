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

rust_micro_rpc_service(
    name = "service",
    srcs = [":proto"],
)
