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
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "lib",
    srcs = [
        "src/app_service.rs",
        "src/lib.rs",
    ],
    crate_name = "oak_containers_hello_world_trusted_app",
    deps = [
        ":build",
        "//oak_containers_sdk",
        "//oak_crypto",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_binary(
    name = "oak_containers_hello_world_trusted_app",
    srcs = ["src/main.rs"],
    deps = [
        ":lib",
        "//oak_containers_sdk",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:tokio",
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
        "//oak_containers_hello_world_trusted_app/proto:interface_proto",
        "//proto/crypto:crypto_proto",
    ],
    tools = [
        "@com_google_protobuf//:protoc",
    ],
    deps = [
        "//oak_grpc_utils",
        "@oak_crates_index//:prost-build",
    ],
)
