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

load("@oak_bzlmod//bazel:defs.bzl", "oci_runtime_bundle")
load("@rules_cc//cc:cc_test.bzl", "cc_test")
load("@rules_oci//oci:defs.bzl", "oci_image")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
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
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand",
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
    name = "encryption",
    srcs = ["src/encryption.rs"],
    deps = [
        "@oak_crates_index//:aes-gcm-siv",
        "@oak_crates_index//:anyhow",
    ],
)

rust_library(
    name = "log",
    srcs = ["src/log.rs"],
    deps = [
        "//src/icing",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
    ],
)

rust_library(
    name = "metrics",
    srcs = ["src/metrics.rs"],
    deps = [
        "//proto:sealed_memory_rust_proto",
        "@oak//oak_containers/agent:oak_containers_agent",
        "@oak_crates_index//:lazy_static",
        "@oak_crates_index//:opentelemetry",
        "@oak_crates_index//:prost",
    ],
)

rust_library(
    name = "external_db_client",
    srcs = ["src/external_db_client.rs"],
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        ":log",
        ":metrics",
        "//proto:sealed_memory_rust_proto",
        "//proto/grpc:sealed_memory_grpc_proto",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:opentelemetry",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rand",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

rust_library(
    name = "private_memory_server_lib",
    srcs = [
        "src/lib.rs",
    ],
    deps = [
        ":encryption",
        ":external_db_client",
        ":log",
        ":metrics",
        "//app",
        "//database",
    ],
)

rust_library(
    name = "client",
    srcs = ["src/client.rs"],
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//proto:sealed_memory_rust_proto",
        "//proto/grpc:sealed_memory_grpc_proto",
        "@oak//oak_proto_rust",
        "@oak//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tonic",
    ],
)

rust_binary(
    name = "private_memory_server",
    srcs = ["src/main.rs"],
    deps = [
        ":private_memory_server_lib",
        "@oak//oak_sdk/containers:oak_sdk_containers",
        "@oak//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:log",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
    ],
)

cc_test(
    name = "icing_porting_test",
    srcs = ["test/icing_porting_test.cc"],
    deps = [
        "@com_google_googletest//:gtest_main",
        "@icing",
    ],
)

rust_library(
    name = "private_memory_test_utils",
    srcs = ["test/test_utils.rs"],
    deps = [
        ":private_memory_server_lib",
        ":private_memory_test_database_server_lib",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
    ],
)

rust_test(
    name = "server_e2e_test",
    srcs = ["test/server_e2e_test.rs"],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        ":client",
        ":private_memory_server_lib",
        ":private_memory_test_database_server_lib",
        ":private_memory_test_utils",
        "//proto:sealed_memory_rust_proto",
        "//proto/grpc:sealed_memory_grpc_proto",
        "@oak//oak_client",
        "@oak//oak_client/tonic:oak_client_tonic",
        "@oak//oak_crypto",
        "@oak//oak_proto_rust",
        "@oak//oak_proto_rust/grpc",
        "@oak//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:futures-util",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

rust_test(
    name = "proto_serialization_test",
    srcs = ["test/proto_serialization_test.rs"],
    deps = [
        "//proto:sealed_memory_rust_proto",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde_json",
    ],
)

rust_test(
    name = "client_test",
    srcs = ["test/client_test.rs"],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        ":client",
        ":private_memory_server_lib",
        ":private_memory_test_database_server_lib",
        ":private_memory_test_utils",
        "//proto:sealed_memory_rust_proto",
        "//proto/grpc:sealed_memory_grpc_proto",
        "@oak//oak_client",
        "@oak//oak_client/tonic:oak_client_tonic",
        "@oak//oak_crypto",
        "@oak//oak_proto_rust",
        "@oak//oak_proto_rust/grpc",
        "@oak//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:futures-util",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

rust_test(
    name = "external_db_client_test",
    srcs = ["test/external_db_client_test.rs"],
    deps = [
        ":external_db_client",
        ":private_memory_test_database_server_lib",
        "//proto:sealed_memory_rust_proto",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

rust_test(
    name = "search_test",
    srcs = ["test/search_test.rs"],
    deps = [
        "//database",
        "//proto:sealed_memory_rust_proto",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:prost-types",
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
    config_patch = 'with(.process.rlimits ; .[] | select(.type == "RLIMIT_NOFILE") | .hard = 524288) | with(.process.rlimits ; .[] | select(.type == "RLIMIT_NOFILE") | .soft = 524288)',
    image = ":image",
)
