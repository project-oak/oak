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
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test", "rust_test_suite")
load("//bazel:defs.bzl", "either_platform")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_echo_service",
    srcs = glob(["src/*.rs"]),
    proc_macro_deps = [
        "@oak_crates_index//:prost-derive",
    ],
    target_compatible_with = either_platform([
        "//:x86_64-linux-setting",  # Needed to run unit tests.
        "//:x86_64-none-setting",
    ]),
    deps = [
        ":build",
        "//micro_rpc",
        "//oak_attestation",
        "//oak_proto_rust",
        "//oak_restricted_kernel_sdk",
        "@oak_crates_index//:hashbrown",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
    ],
)

rust_test(
    name = "oak_echo_service_test",
    size = "small",
    crate = ":oak_echo_service",
)

rust_test_suite(
    name = "oak_echo_service_integration_test",
    srcs = ["tests/integration_test.rs"],
    deps = [
        ":oak_echo_service",
        "//oak_restricted_kernel_sdk",
    ],
)

cargo_build_script(
    name = "build",
    srcs = ["build.rs"],
    build_script_env = {
        "PROTOC": "$(execpath @com_google_protobuf//:protoc)",
        "DESCRIPTOR_PROTO_PATH": "$(location @com_google_protobuf//:descriptor_proto_srcs)",
    },
    crate_features = ["bazel"],
    data = [
        "//proto/session:messages_proto",
        "//proto/session:service_streaming_proto",
        "//testing/oak_echo_service/proto",
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
