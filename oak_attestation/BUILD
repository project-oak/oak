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
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")
load("//bazel:defs.bzl", "any_platform")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_attestation",
    srcs = glob(["src/**"]),
    target_compatible_with = any_platform([
        "//:aarch64-apple-setting",
        "//:x86_64-linux-setting",
        "//:x86_64-none-no_avx-setting",
        "//:x86_64-none-setting",
    ]),
    deps = [
        "//oak_attestation_types",
        "//oak_dice",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:bytes",
        "@oak_crates_index//:ciborium",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:zeroize",
    ],
)

rust_test(
    name = "oak_attestation_tests",
    crate = ":oak_attestation",
    deps = [
        "@oak_crates_index//:googletest",
    ],
)
