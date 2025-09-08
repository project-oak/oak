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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test", "rust_test_suite")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

RESULT_SRC = ["src/results.rs"]

# The target only for parsing attestation verification results, to provide a
# minimal set of dependencies for oak_session.
rust_library(
    name = "oak_attestation_verification_results",
    srcs = RESULT_SRC,
    deps = [
        "//oak_proto_rust",
    ],
)

rust_test(
    name = "results_unit_tests",
    crate = ":oak_attestation_verification_results",
)

rust_library(
    name = "oak_attestation_verification",
    srcs = glob(
        ["src/**"],
        exclude = RESULT_SRC,
    ),
    compile_data = [
        "//oak_attestation_verification/data:amd_ask_certs",
        "//oak_attestation_verification/data:intel_pck_root",
    ],
    deps = [
        ":oak_attestation_verification_results",
        "//oak_attestation_verification_types",
        "//oak_crypto",
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_sev_snp_attestation_report",
        "//oak_tdx_quote",
        "//oak_time",
        "//tr/digest_util",
        "//tr/intoto",
        "//tr/key_util",
        "//tr/rekor",
        "//tr/verify_endorsement",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:const-oid",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:ecdsa",
        "@oak_crates_index//:hashbrown",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:itertools",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:p384",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rsa",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:thiserror",
        "@oak_crates_index//:x509-cert",
        "@oak_crates_index//:zerocopy",
    ],
)

rust_test(
    name = "unit_tests",
    compile_data = [
        "//oak_attestation_verification/data:amd_ark_certs",
        "//oak_attestation_verification/data:amd_ask_certs",
    ],
    crate = ":oak_attestation_verification",
    crate_features = ["std"],
    data = [
        "//oak_attestation_verification/data:amd_ark_certs",
        "//oak_attestation_verification/data:amd_ask_certs",
    ],
    deps = [
        ":test_util",
        "//oak_file_utils",
        "@oak_crates_index//:rand_core",
    ],
)

rust_test_suite(
    name = "integration_tests",
    srcs = [
        "tests/endorsement_tests.rs",
        "tests/policy_tests.rs",
        "tests/verifier_tests.rs",
    ],
    data = [
        "//oak_attestation_verification/data:amd_ark_certs",
        "//oak_attestation_verification/data:amd_ask_certs",
        "//oak_attestation_verification/testdata:fake_attestation",
    ],
    deps = [
        ":oak_attestation_verification",
        ":test_util",
        "//oak_attestation_verification_types",
        "//oak_file_utils",
        "//oak_proto_rust",
        "//oak_sev_snp_attestation_report",
        "//oak_time",
        "//tr/digest_util",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:x509-cert",
        "@oak_crates_index//:zerocopy",
    ],
)

rust_library(
    name = "oak_attestation_verification_with_regex",
    srcs = glob(["src/**"]),
    compile_data = [
        "//oak_attestation_verification/data:amd_ask_certs",
        "//oak_attestation_verification/data:intel_pck_root",
    ],
    crate_features = ["regex"],
    deps = [
        ":oak_attestation_verification_results",
        "//oak_attestation_verification_types",
        "//oak_crypto",
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_sev_snp_attestation_report",
        "//oak_tdx_quote",
        "//oak_time",
        "//tr/digest_util",
        "//tr/intoto",
        "//tr/key_util",
        "//tr/rekor",
        "//tr/verify_endorsement",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:const-oid",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:ecdsa",
        "@oak_crates_index//:hashbrown",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:itertools",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:p384",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:regex-lite",
        "@oak_crates_index//:rsa",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:thiserror",
        "@oak_crates_index//:x509-cert",
        "@oak_crates_index//:zerocopy",
    ],
)

rust_test(
    name = "unit_tests_with_regex",
    compile_data = [
        "//oak_attestation_verification/data:amd_ark_certs",
        "//oak_attestation_verification/data:amd_ask_certs",
    ],
    crate = ":oak_attestation_verification_with_regex",
    crate_features = ["std"],
    data = [
        "//oak_attestation_verification/data:amd_ark_certs",
        "//oak_attestation_verification/data:amd_ask_certs",
    ],
    deps = [
        ":test_util",
        "//oak_crypto",
        "//oak_file_utils",
        "@oak_crates_index//:rand_core",
    ],
)

rust_test_suite(
    name = "integration_tests_with_regex",
    srcs = [
        "tests/endorsement_tests.rs",
        "tests/policy_tests.rs",
        "tests/verifier_tests.rs",
    ],
    aliases = {":oak_attestation_verification_with_regex": "oak_attestation_verification"},
    crate_features = ["regex"],
    data = [
        "//oak_attestation_verification/data:amd_ark_certs",
        "//oak_attestation_verification/data:amd_ask_certs",
        "//oak_attestation_verification/testdata:fake_attestation",
    ],
    deps = [
        ":oak_attestation_verification_with_regex",
        ":test_util",
        "//oak_attestation_verification_types",
        "//oak_file_utils",
        "//oak_proto_rust",
        "//oak_sev_snp_attestation_report",
        "//oak_time",
        "//tr/digest_util",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:x509-cert",
        "@oak_crates_index//:zerocopy",
    ],
)

rust_library(
    name = "test_util",
    srcs = glob(["test_util/**"]),
    data = [
        "//oak_attestation_verification/testdata:cb_attestation",
        "//oak_attestation_verification/testdata:endorsement",
        "//oak_attestation_verification/testdata:fake_attestation",
        "//oak_attestation_verification/testdata:genoa_oc_attestation",
        "//oak_attestation_verification/testdata:milan_oc_release_attestation",
        "//oak_attestation_verification/testdata:milan_oc_staging_attestation",
        "//oak_attestation_verification/testdata:milan_rk_release_attestation",
        "//oak_attestation_verification/testdata:milan_rk_staging_attestation",
        "//oak_attestation_verification/testdata:tdx_oc_attestation",
        "//oak_attestation_verification/testdata:turin_oc_attestation",
    ],
    deps = [
        "//oak_file_utils",
        "//oak_proto_rust",
        "//oak_sev_snp_attestation_report",
        "//oak_time",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:zerocopy",
    ],
)

# Invoke by:
# bazel run oak_attestation_verification:benches -- --bench
rust_test(
    name = "benches",
    srcs = ["tests/benchmarks.rs"],
    deps = [
        ":oak_attestation_verification",
        ":test_util",
        "//oak_attestation_verification_types",
        "//oak_proto_rust",
        "//oak_time",
    ],
)
