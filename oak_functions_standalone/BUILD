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

exports_files(["README.md"])

rust_library(
    name = "lib",
    srcs = [
        "src/lib.rs",
        "tests/integration_test.rs",
    ],
    compile_data = [":README.md"],
    crate_features = [
        "deny_sensitive_logging",
    ],
    crate_name = "oak_functions_standalone",
    deps = [
        "//micro_rpc",
        "//oak_attestation",
        "//oak_crypto",
        "//oak_debug_service",
        "//oak_functions_abi",
        "//oak_functions_service:lib_unrestricted",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_session",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:http",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:tempfile",
        "@oak_crates_index//:tikv-jemallocator",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:tower",
        "@oak_crates_index//:tower-http",
    ],
)

rust_binary(
    name = "oak_functions_standalone",
    srcs = ["src/main.rs"],
    crate_features = [
        "deny_sensitive_logging",
    ],
    data = [
        "//oak_functions/examples/echo",
    ],
    deps = [
        ":lib",
        "//oak_containers/agent",
        "//oak_crypto",
        "//oak_functions_service:lib_unrestricted",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:opentelemetry",
        "@oak_crates_index//:opentelemetry-otlp",
        "@oak_crates_index//:opentelemetry_sdk",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:tikv-jemallocator",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)

rust_test(
    name = "lib_test",
    crate = ":lib",
)

rust_test(
    name = "oak_functions_standalone_integration_test",
    size = "large",
    srcs = ["tests/integration_test.rs"],
    data = [
        "//oak_functions/examples/echo",
        "//oak_functions/examples/key_value_lookup",
    ],
    deps = [
        ":lib",
        "//micro_rpc",
        "//oak_client",
        "//oak_containers/agent",
        "//oak_crypto",
        "//oak_functions_client:lib",
        "//oak_functions_service:lib_unrestricted",
        "//oak_functions_test_utils",
        "//oak_launcher_utils",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_session",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:opentelemetry",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tokio-stream",
        "@oak_crates_index//:tonic",
    ],
)
