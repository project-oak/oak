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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_gcp_examples_echo_enclave_app",
    srcs = [
        "src/app.rs",
        "src/app_service.rs",
        "src/lib.rs",
    ],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        "//oak_containers_sdk",
        "//oak_crypto",
        "//oak_gcp/examples/echo/proto:echo_rust_proto",
        "//oak_proto_rust",
        "//oak_session",
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
    name = "integration_test",
    srcs = ["tests/integration_test.rs"],
    proc_macro_deps = ["@oak_crates_index//:async-trait"],
    deps = [
        ":oak_gcp_examples_echo_enclave_app",
        "//oak_client",
        "//oak_crypto",
        "//oak_gcp/examples/echo/proto:echo_rust_proto",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:futures-util",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
    ],
)

rust_binary(
    name = "bin/oak_gcp_examples_echo_enclave_app",
    srcs = ["src/main.rs"],
    deps = [
        ":oak_gcp_examples_echo_enclave_app",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:tokio",
    ],
)
