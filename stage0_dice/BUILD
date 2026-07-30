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
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

_STAGE0_DICE_DEPS = [
    "//oak_dice",
    "//oak_proto_rust",
    "//oak_sev_snp_attestation_report",
    "@oak_crates_index//:coset",
    "@oak_crates_index//:hex",
    "@oak_crates_index//:hkdf",
    "@oak_crates_index//:p256",
    "@oak_crates_index//:prost",
    "@oak_crates_index//:prost-types",
    "@oak_crates_index//:rand_core",
    "@oak_crates_index//:sha2",
    "@oak_crates_index//:zerocopy",
]

_STAGE0_DICE_TARGET_COMPATIBLE_WITH = any_platform([
    "//:x86_64-none-setting",
    "//:x86_64-none-no_avx-setting",
    "//:x86_64-linux-setting",  # Needed for unit testing of stage0.
])

rust_library(
    name = "stage0_dice",
    srcs = glob(["src/**"]),
    crate_name = "oak_stage0_dice",
    target_compatible_with = _STAGE0_DICE_TARGET_COMPATIBLE_WITH,
    deps = _STAGE0_DICE_DEPS,
)

rust_library(
    name = "stage0_dice_fixed_key",
    testonly = True,
    srcs = glob(["src/**"]),
    crate_features = ["fixed_root_key"],
    crate_name = "oak_stage0_dice",
    target_compatible_with = _STAGE0_DICE_TARGET_COMPATIBLE_WITH,
    deps = _STAGE0_DICE_DEPS + [
        "@oak_crates_index//:zeroize",
    ],
)

rust_test(
    name = "stage0_dice_test",
    size = "small",
    crate = ":stage0_dice_fixed_key",
    crate_features = ["fixed_root_key"],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "@oak_crates_index//:googletest",
    ],
)
