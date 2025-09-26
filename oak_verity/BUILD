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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_verity",
    srcs = glob(["src/**/*.rs"]),
    deps = [
        "//oak_functions_abi",
        "//oak_functions_service:lib_unrestricted",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:log",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:sha2",
    ],
)

rust_test(
    name = "oak_verity_test",
    crate = ":oak_verity",
)

rust_test(
    name = "oak_verity_integration_test",
    srcs = ["tests/integration_test.rs"],
    data = ["//oak_functions/examples/echo"],
    deps = [
        ":oak_verity",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
    ],
)
