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
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(licenses = ["notice"])

rust_library(
    name = "lib",
    srcs = ["src/lib.rs"],
    deps = [
        ":build",
        "@oak2//oak_proto_rust",
        "@oak_crates_index//:prost",
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
    },
    data = [
        "//test_import_microrpc_protos/proto:test_protos",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "@oak2//oak_grpc_utils",
        # "//oak_proto_build_utils",
        "@oak_crates_index//:prost-build",
    ],
)

rust_test(
    name = "test",
    size = "small",
    crate = ":lib",
    deps = ["@oak2//micro_rpc"],
)
