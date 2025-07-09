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
load("//bazel:defs.bzl", "any_platform")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_tdx_quote",
    srcs = glob(["src/**"]),
    crate_name = "oak_tdx_quote",
    proc_macro_deps = [
        "@oak_crates_index//:strum_macros",
    ],
    target_compatible_with = any_platform([
        "//:aarch64-apple-setting",
        "//:x86_64-linux-setting",
        "//:x86_64-none-setting",
        "//:x86_64-none-no_avx-setting",
        "//:wasm32-none-setting",
    ]),
    deps = [
        "@oak_crates_index//:bitflags",
        "@oak_crates_index//:nom",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:thiserror",
    ],
)

rust_test(
    name = "oak_tdx_quote_tests",
    crate = ":oak_tdx_quote",
    data = [
        "//oak_attestation_verification/testdata:oc_attestation_tdx",
    ],
    deps = [
        "//oak_file_utils",
        "//oak_proto_rust",
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:prost",
    ],
)
