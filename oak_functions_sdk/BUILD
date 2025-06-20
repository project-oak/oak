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

package(
    default_visibility = ["//:default_visibility"],
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
        "//oak_proto_rust/micro_rpc",
        "@oak_crates_index//:prost",
    ],
)

rust_test_suite(
    name = "integration_tests",
    srcs = glob(["tests/**"]),
    data = [
        "//oak_functions_sdk/tests/lookup_module",
        "//oak_functions_sdk/tests/testing_module",
    ],
    deps = [
        ":oak_functions_sdk",
        "//oak_file_utils",
        "//oak_functions_abi",
        "//oak_functions_service:lib",
        "//oak_functions_test_utils",
        "@oak_crates_index//:lazy_static",
        "@oak_crates_index//:tokio",
    ],
)
