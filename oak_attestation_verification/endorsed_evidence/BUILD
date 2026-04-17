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
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "endorsed_evidence_assertion_verifier",
    srcs = glob(["*.rs"]),
    deps = [
        "//oak_attestation_verification:oak_attestation_verification_results",
        "//oak_attestation_verification_types",
        "//oak_crypto",
        "//oak_proto_rust",
        "//oak_time",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
    ],
)

rust_test(
    name = "endorsed_evidence_assertion_verifier_tests",
    crate = ":endorsed_evidence_assertion_verifier",
    data = [
        "//oak_attestation_verification/endorsed_evidence/testdata",
    ],
    deps = [
        "//oak_attestation_verification",
        "//oak_attestation_verification:test_util",
        "//oak_file_utils",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:prost",
    ],
)
