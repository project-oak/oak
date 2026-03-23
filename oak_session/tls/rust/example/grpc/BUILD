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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")
load("@rules_shell//shell:sh_test.bzl", "sh_test")
load("//oak_grpc_utils:build_defs.bzl", "rust_tonic_grpc_service")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_tonic_grpc_service(
    name = "tls_over_grpc_rust_proto",
    srcs = ["//oak_session/tls/example/grpc:tls_over_grpc_proto"],
    crate_name = "oak_session_tls_example_grpc_proto",
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//oak_proto_rust",
    ],
)

rust_binary(
    name = "server_rust",
    srcs = ["server.rs"],
    data = ["//oak_session/tls/testing:test_keys"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":tls_over_grpc_rust_proto",
        "//oak_session/tls/rust:oak_session_tls",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:rustls-pki-types",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_test(
    name = "server_rust_test",
    srcs = ["server.rs"],
    data = ["//oak_session/tls/testing:test_keys"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":tls_over_grpc_rust_proto",
        "//oak_session/tls/rust:oak_session_tls",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:rustls-pki-types",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_binary(
    name = "client_rust",
    srcs = ["client.rs"],
    data = ["//oak_session/tls/testing:test_keys"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        ":tls_over_grpc_rust_proto",
        "//oak_session/tls/rust:oak_session_tls",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:rustls-pki-types",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

sh_test(
    name = "client_server_rust_test",
    srcs = ["//oak_session/tls/example/grpc:client_server_test.sh"],
    data = [
        ":client_rust",
        ":server_rust",
    ],
    env = {
        "CLIENT": "$(location :client_rust)",
        "SERVER": "$(location :server_rust)",
    },
    target_compatible_with = ["@platforms//os:linux"],
)

sh_test(
    name = "client_server_cc_rust_test",
    srcs = ["//oak_session/tls/example/grpc:client_server_test.sh"],
    data = [
        ":client_rust",
        "//oak_session/tls/example/grpc:server",
    ],
    env = {
        "CLIENT": "$(location :client_rust)",
        "SERVER": "$(location //oak_session/tls/example/grpc:server)",
    },
    target_compatible_with = ["@platforms//os:linux"],
)

sh_test(
    name = "client_server_rust_cc_test",
    srcs = ["//oak_session/tls/example/grpc:client_server_test.sh"],
    data = [
        ":server_rust",
        "//oak_session/tls/example/grpc:client",
    ],
    env = {
        "CLIENT": "$(location //oak_session/tls/example/grpc:client)",
        "SERVER": "$(location :server_rust)",
    },
    target_compatible_with = ["@platforms//os:linux"],
)
