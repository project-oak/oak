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

rust_library(
    name = "oak_sev_guest",
    srcs = glob(["src/**"]),
    crate_features = [
        "rust-crypto",
    ],
    target_compatible_with = any_platform([
        "//:x86_64-none-setting",
        "//:x86_64-none-no_avx-setting",
        "//:x86_64-linux-setting",  # Needed for unit testing.
    ]),
    deps = [
        "//oak_sev_snp_attestation_report",
        "@oak_crates_index//:aes-gcm",
        "@oak_crates_index//:bitflags",
        "@oak_crates_index//:lock_api",
        "@oak_crates_index//:snafu",
        "@oak_crates_index//:spinning_top",
        "@oak_crates_index//:static_assertions",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:zerocopy",
    ],
)

rust_library(
    name = "oak_sev_guest_no_rust_crypto",
    srcs = glob(["src/**"]),
    crate_name = "oak_sev_guest",
    target_compatible_with = any_platform([
        "//:x86_64-none-setting",
        "//:x86_64-none-no_avx-setting",
        "//:x86_64-linux-setting",  # Needed for unit testing.
    ]),
    deps = [
        "//oak_sev_snp_attestation_report",
        "@oak_crates_index//:bitflags",
        "@oak_crates_index//:lock_api",
        "@oak_crates_index//:snafu",
        "@oak_crates_index//:spinning_top",
        "@oak_crates_index//:static_assertions",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:zerocopy",
    ],
)

rust_test(
    name = "oak_sev_guest_test",
    size = "small",
    crate = ":oak_sev_guest",
)
