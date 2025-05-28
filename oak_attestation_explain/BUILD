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

rust_library(
    name = "oak_attestation_explain",
    srcs = glob(["src/**"]),
    deps = [
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:serde_yaml",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:zerocopy_08",
    ],
)

rust_test_suite(
    name = "oak_attestation_explain_integration_tests",
    srcs = glob(["tests/**/*.rs"]),
    compile_data = glob(["testdata/**"]),
    deps = [
        "//oak_attestation_explain",
        "//oak_attestation_verification",
        "//oak_proto_rust",
        "@oak_crates_index//:prost",
    ],
)
