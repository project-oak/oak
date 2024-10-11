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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_library", "rust_test_suite")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

filegroup(
    name = "testdata",
    srcs = glob(["testdata/**"]),
)

rust_library(
    name = "lib",
    srcs = glob(["src/**"]),
    crate_name = "oak_attestation_integration_tests",
    deps = [
        "//oak_attestation_integration_test_utils",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:assert-json-diff",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:tokio",
    ],
)

rust_binary(
    name = "update_testdata_assert_no_breaking_changes",
    srcs = ["src/main.rs"],
    data = [
        ":testdata",
        "//proto:digest_proto",
        "//proto/attestation:attachment_proto",
        "//proto/attestation:dice_proto",
        "//proto/attestation:endorsement_proto",
        "//proto/attestation:eventlog_proto",
        "//proto/attestation:evidence_proto",
        "//proto/attestation:expected_value_proto",
        "//proto/attestation:reference_value_proto",
        "//proto/attestation:tcb_version_proto",
        "//proto/attestation:verification_proto",
        "//proto/crypto:crypto_proto",
        "//proto/session:service_streaming_proto",
        "//proto/session:session_proto",
    ],
    deps = [
        ":lib",
        "//oak_attestation_integration_test_utils",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:tokio",
    ],
)

rust_test_suite(
    name = "oak_attestation_integration_tests_tests",
    srcs = glob(["tests/**"]),
    data = [
        ":testdata",
        "//proto:digest_proto",
        "//proto/attestation:attachment_proto",
        "//proto/attestation:dice_proto",
        "//proto/attestation:endorsement_proto",
        "//proto/attestation:eventlog_proto",
        "//proto/attestation:evidence_proto",
        "//proto/attestation:expected_value_proto",
        "//proto/attestation:reference_value_proto",
        "//proto/attestation:tcb_version_proto",
        "//proto/attestation:verification_proto",
        "//proto/crypto:crypto_proto",
        "//proto/session:service_streaming_proto",
        "//proto/session:session_proto",
    ],
    deps = [
        ":lib",
        "//oak_attestation",
        "//oak_attestation_integration_test_utils",
        "//oak_attestation_verification",
        "//oak_containers_sdk",
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_restricted_kernel_sdk",
        "//stage0_dice",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_chacha",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:tokio",
    ],
)
