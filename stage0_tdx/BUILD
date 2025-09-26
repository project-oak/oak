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
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "stage0_tdx",
    srcs = glob(["src/**/*.rs"]),
    aliases = {"@//stage0": "oak_stage0"},
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_dice",
        "//oak_linux_boot_params",
        "//oak_proto_rust",
        "//oak_tdx_guest",
        "//stage0",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:lock_api",
        "@oak_crates_index//:log",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:spinning_top",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)

rust_library(
    name = "stage0_tdx_for_test",
    srcs = glob(["src/**/*.rs"]),
    aliases = {"@//stage0:stage0_for_test": "oak_stage0"},
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_dice",
        "//oak_linux_boot_params",
        "//oak_proto_rust",
        "//oak_tdx_guest",
        "//stage0:stage0_for_test",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:lock_api",
        "@oak_crates_index//:log",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:spinning_top",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)

rust_test(
    name = "stage0_tdx_test",
    size = "small",
    crate = ":stage0_tdx_for_test",
    deps = [
        "//stage0_dice",
    ],
)
