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
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "lib",
    srcs = glob(
        ["src/**"],
        exclude = ["src/main.rs"],
    ),
    crate_name = "oak_functions_launcher",
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//micro_rpc",
        "//oak_client",
        "//oak_launcher_utils",
        "//oak_proto_rust",
        "//oak_proto_rust/grpc",
        "//oak_proto_rust/micro_rpc",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:async-stream",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:futures",
        "@oak_crates_index//:hashbrown",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:tonic",
        "@oak_crates_index//:ubyte",
    ],
)

rust_test(
    name = "oak_functions_launcher_test",
    size = "small",
    crate = ":lib",
)

rust_binary(
    name = "oak_functions_launcher",
    srcs = ["src/main.rs"],
    deps = [
        ":lib",
        "//oak_client",
        "//oak_functions_abi",
        "//oak_launcher_utils",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:regex",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:ubyte",
    ],
)

# This test is currently broken and disabled because the Bazel-built stage0 is broken.
rust_test(
    name = "oak_functions_launcher_integration_test",
    size = "large",
    srcs = ["tests/integration_test.rs"],
    data = [
        "mock_lookup_data",
        ":oak_functions_launcher",
        "//cc/client:cli",
        "//enclave_apps/oak_functions_enclave_app",
        "//enclave_apps/oak_orchestrator",
        "//java/src/main/java/com/google/oak/client/oak_functions_client",
        "//oak_functions/examples/echo",
        "//oak_functions/examples/key_value_lookup",
        "//oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin",
        "//stage0_bin",
    ],
    env = {
        "RUST_LOG": "debug",
    },
    deps = [
        ":lib",
        "//micro_rpc",
        "//oak_client",
        "//oak_functions_client:lib",
        "//oak_functions_test_utils",
        "//oak_launcher_utils",
        "//oak_proto_rust/micro_rpc",
        "@oak_crates_index//:log",
        "@oak_crates_index//:tokio",
        "@oak_crates_index//:ubyte",
        "@oak_crates_index//:which",
    ],
)
