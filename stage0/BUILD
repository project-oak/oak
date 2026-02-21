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
    name = "stage0",
    srcs = glob(["src/**"]),
    crate_features = [
        "sev",
        # Enable this if you want to enable kernel hashes
        # "sev_kernel_hashes",
    ],
    target_compatible_with = any_platform([
        "//:x86_64-none-setting",
        "//:x86_64-none-no_avx-setting",
        "//:x86_64-linux-setting",  # Needed for unit testing.
    ]),
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_core",
        "//oak_dice",
        "//oak_linux_boot_params",
        "//oak_proto_rust",
        "//oak_sev_guest",
        "//oak_sev_snp_attestation_report",
        "//sev_serial",
        "//stage0_dice",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:bitflags",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:elf",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:hkdf",
        "@oak_crates_index//:linked_list_allocator",
        "@oak_crates_index//:log",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:spinning_top",
        "@oak_crates_index//:static_assertions",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)

rust_library(
    name = "stage0_for_test",
    srcs = glob(["src/**"]),
    crate_features = [
        "sev",
        "stage0_test",
    ],
    target_compatible_with = any_platform([
        "//:x86_64-linux-setting",  # Needed for unit testing.
    ]),
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_core",
        "//oak_dice",
        "//oak_linux_boot_params",
        "//oak_proto_rust",
        "//oak_sev_guest",
        "//oak_sev_snp_attestation_report",
        "//sev_serial",
        "//stage0_dice",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:bitflags",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:elf",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:hkdf",
        "@oak_crates_index//:linked_list_allocator",
        "@oak_crates_index//:log",
        "@oak_crates_index//:mockall",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:spinning_top",
        "@oak_crates_index//:static_assertions",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:x86_64",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)

rust_test(
    name = "stage0_test",
    size = "small",
    crate = ":stage0_for_test",
    data = ["testdata/table_loader"],
    deps = [
        "//oak_file_utils",
        "@oak_crates_index//:googletest",
    ],
)
