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

load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_library(
    name = "stage0_sev",
    srcs = glob(["src/**/*.rs"]),
    aliases = {"//stage0": "oak_stage0"},
    # Enable if you want to use kernel hashes
    # crate_features = ["sev_kernel_hashes"],
    deps = [
        "//oak_attestation",
        "//oak_core",
        "//oak_dice",
        "//oak_linux_boot_params",
        "//oak_sev_guest",
        "//oak_sev_snp_attestation_report",
        "//stage0",
        "//stage0_dice",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:log",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:spinning_top",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)
