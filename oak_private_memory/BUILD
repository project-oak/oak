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

load("@oak//bazel:defs.bzl", "oci_runtime_bundle")
load("@rules_oci//oci:defs.bzl", "oci_image")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")

package(
    licenses = ["notice"],
)

rust_library(
    name = "private_memory_test_database_server_lib",
    srcs = [
        "test/database/lib.rs",
        "test/database/service.rs",
    ],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        "//proto:sealed_memory_rust_proto",
        "//proto/grpc:sealed_memory_grpc_proto",
        "@oak//oak_crypto",
        "@oak//oak_proto_rust",
        "@oak//oak_sdk/server/v1:oak_sdk_server_v1",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_test(
    name = "private_memory_test",
    crate = ":private_memory_server_lib",
    deps = [
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:tempfile",
    ],
)

rust_library(
    name = "private_memory_server_lib",
    srcs = [
        "src/app.rs",
        "src/app_config.rs",
        "src/app_service.rs",
        "src/database.rs",
        "src/encryption.rs",
        "src/lib.rs",
    ],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        "//proto:sealed_memory_rust_proto",
        "//proto/grpc:sealed_memory_grpc_proto",
        "//src/icing",
        "@cxx.rs//:cxx",
        "@oak//oak_crypto",
        "@oak//oak_proto_rust",
        "@oak//oak_sdk/server/v1:oak_sdk_server_v1",
        "@oak//oak_session",
        "@oak_crates_index//:aes-gcm",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:bincode",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tempfile",
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
        "@oak//oak_sdk/containers:oak_sdk_containers",
        "@oak//oak_sdk/server/v1:oak_sdk_server_v1",
        "@oak//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
    ],
)

cc_binary(
    name = "icing_porting_test",
    srcs = ["test/icing_porting_test.cc"],
    deps = [
        "@com_google_googletest//:gtest_main",
        "@icing",
    ],
)

rust_test(
    name = "standalone_test",
    srcs = ["test/standalone_test.rs"],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        ":private_memory_server_lib",
        ":private_memory_test_database_server_lib",
        "//proto:sealed_memory_rust_proto",
        "//proto/grpc:sealed_memory_grpc_proto",
        "@oak//oak_client",
        "@oak//oak_client/tonic:oak_client_tonic",
        "@oak//oak_crypto",
        "@oak//oak_proto_rust",
        "@oak//oak_proto_rust/grpc",
        "@oak//oak_sdk/server/v1:oak_sdk_server_v1",
        "@oak//oak_sdk/standalone:oak_sdk_standalone",
        "@oak//oak_session",
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
