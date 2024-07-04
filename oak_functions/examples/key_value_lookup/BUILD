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

load("@rules_rust//rust:defs.bzl", "rust_shared_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_shared_library(
    name = "key_value_lookup",
    srcs = ["module/src/lib.rs"],
    platform = "//:wasm32-unknown-unknown",
    deps = ["//oak_functions_sdk"],
)

rust_test(
    name = "test",
    srcs = ["module/src/tests.rs"],
    crate_features = ["bazel"],
    data = [
        ":key_value_lookup",
        "//oak_functions_launcher",
    ],
    deps = [
        "//micro_rpc",
        "//micro_rpc_build",
        "//oak_client",
        "//oak_functions_abi",
        "//oak_functions_client:lib",
        "//oak_functions_test_utils",
        "//xtask:lib",
        "@oak_crates_index//:log",
        "@oak_crates_index//:maplit",
        "@oak_crates_index//:pretty_assertions",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:tokio",
    ],
)
