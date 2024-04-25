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
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_attestation_verification",
    srcs = glob(["src/**"]),
    compile_data = [
        "//oak_attestation_verification/data:ask_milan.pem",
    ],
    deps = [
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_sev_snp_attestation_report",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:ecdsa",
        "@oak_crates_index//:getrandom",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:p384",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rsa",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:time",
        "@oak_crates_index//:x509-cert",
        "@oak_crates_index//:zerocopy",
    ],
)

rust_library(
    name = "oak_attestation_verification_with_regex",
    srcs = glob(["src/**"]),
    compile_data = [
        "//oak_attestation_verification/data:ask_milan.pem",
    ],
    crate_features = ["regex"],
    deps = [
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_sev_snp_attestation_report",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:ecdsa",
        "@oak_crates_index//:getrandom",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:p384",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:regex",
        "@oak_crates_index//:rsa",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:time",
        "@oak_crates_index//:x509-cert",
        "@oak_crates_index//:zerocopy",
    ],
)
