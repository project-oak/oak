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
load("//bazel:defs.bzl", "select_std_crates")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

exports_files(["README.md"])

rust_library(
    name = "oak_functions_sdk",
    srcs = glob(["src/**"]),
    compile_data = [":README.md"],
    deps = [
        "//micro_rpc",
        "//oak_functions_abi",
        "//oak_proto_rust",
    ] + select_std_crates(["prost"]),
)

rust_test_suite(
    name = "integration_tests",
    srcs = glob(["tests/**"]),
    crate_features = ["bazel"],  # TODO: b/333064338 remove.
    data = [
        "//oak_functions_sdk/tests/lookup_module",
        "//oak_functions_sdk/tests/testing_module",
    ],
    deps = [
        ":oak_functions_sdk",
        "//oak_functions_abi",
        "//oak_functions_service",
        "//oak_functions_test_utils",
        "@oak_crates_index//:lazy_static",
        "@oak_crates_index//:tokio",
    ],
)
