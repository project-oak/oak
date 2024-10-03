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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test_suite")
load("//bazel:defs.bzl", "either_platform")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

DEPS = [
    "//micro_rpc",
    "//oak_core",
    "//oak_crypto",
    "//oak_proto_rust",
    "//oak_proto_rust/micro_rpc",
    "//oak_restricted_kernel_sdk",
    "@oak_crates_index//:anyhow",
    "@oak_crates_index//:log",
    "@oak_crates_index//:prost",
]

rust_library(
    name = "lib",
    srcs = glob(["src/*.rs"]),
    # The features are inverted on purpose; this means the "default"
    # package will not have sensitive logging enabled.
    crate_features = ["deny_sensitive_logging"],
    crate_name = "oak_functions_enclave_service",
    target_compatible_with = either_platform([
        "//:x86_64-none-setting",
        "//:x86_64-linux-setting",  # Needed to run unit tests.
    ]),
    deps = DEPS + [
        "//oak_functions_service:lib",
    ],
)

rust_library(
    name = "lib_insecure",
    srcs = glob(["src/*.rs"]),
    crate_name = "oak_functions_enclave_service",
    target_compatible_with = either_platform([
        "//:x86_64-none-setting",
        "//:x86_64-linux-setting",  # Needed to run unit tests.
    ]),
    deps = DEPS + [
        "//oak_functions_service:lib_insecure",
    ],
)

rust_test_suite(
    name = "integration_tests",
    srcs = glob(["tests/**"]),
    crate_features = ["bazel"],  # TODO: b/333064338 remove.
    data = [
        "//oak_functions/examples/echo",
        "//oak_functions/examples/invalid_module",
        "//oak_functions/examples/key_value_lookup",
        "//oak_functions_test_module",
    ],
    deps = [
        ":lib",
        "//micro_rpc",
        "//oak_client",
        "//oak_crypto",
        "//oak_functions_service:lib",
        "//oak_functions_test_utils",
        "//oak_proto_rust",
        "//oak_proto_rust/micro_rpc",
        "//oak_restricted_kernel_sdk",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
    ],
)
