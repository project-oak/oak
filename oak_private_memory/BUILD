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

load("@rules_oci//oci:defs.bzl", "oci_image")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")
load("//bazel:defs.bzl", "oci_runtime_bundle")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "private_memory_database_server_lib",
    srcs = [
        "src/database/lib.rs",
        "src/database/service.rs",
    ],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        "//oak_crypto",
        "//oak_private_memory/proto:sealed_memory_rust_proto",
        "//oak_private_memory/proto/grpc:sealed_memory_grpc_proto",
        "//oak_proto_rust",
        "//oak_sdk/server/v1:oak_sdk_server_v1",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_library(
    name = "private_memory_server_lib",
    srcs = [
        "src/app.rs",
        "src/app_config.rs",
        "src/app_service.rs",
        "src/lib.rs",
    ],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        "//oak_crypto",
        "//oak_private_memory/proto:sealed_memory_rust_proto",
        "//oak_private_memory/proto/grpc:sealed_memory_grpc_proto",
        "//oak_proto_rust",
        "//oak_sdk/server/v1:oak_sdk_server_v1",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_binary(
    name = "private_memory_server",
    srcs = ["src/main.rs"],
    deps = [
        ":private_memory_server_lib",
        "//oak_sdk/containers:oak_sdk_containers",
        "//oak_sdk/server/v1:oak_sdk_server_v1",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:tokio",
    ],
)

rust_test(
    name = "standalone_test",
    srcs = ["test/standalone_test.rs"],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        ":private_memory_database_server_lib",
        ":private_memory_server_lib",
        "//oak_client",
        "//oak_client/tonic:oak_client_tonic",
        "//oak_crypto",
        "//oak_private_memory/proto:sealed_memory_rust_proto",
        "//oak_private_memory/proto/grpc:sealed_memory_grpc_proto",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_sdk/server/v1:oak_sdk_server_v1",
        "//oak_sdk/standalone:oak_sdk_standalone",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:futures-util",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

pkg_tar(
    name = "tar",
    srcs = [":private_memory_server"],
    package_dir = "/usr/local/bin",
    strip_prefix = "/oak_private_memory",
)

oci_image(
    name = "image",
    base = "@distroless_cc_debian12",
    entrypoint = ["/usr/local/bin/private_memory_server"],
    tars = [":tar"],
)

oci_runtime_bundle(
    name = "bundle",
    image = ":image",
)
