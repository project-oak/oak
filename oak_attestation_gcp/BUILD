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
    name = "oak_attestation_gcp",
    srcs = glob(["src/**"]),
    compile_data = [
        "//oak_attestation_gcp:data/confidential_space_root.pem",
    ],
    deps = [
        "//oak_attestation_types",
        "//oak_attestation_verification",
        "//oak_attestation_verification_types",
        "//oak_proto_rust",
        "//oak_proto_rust/oak_proto_rust_lib",
        "//oak_time",
        "//tr/intoto",
        "//tr/rekor",
        "//tr/verify_endorsement",
        "//util/digest",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:const-oid",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:http",
        "@oak_crates_index//:jwt",
        "@oak_crates_index//:oci-spec",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:thiserror",
        "@oak_crates_index//:x509-cert",
        "@oak_crates_index//:x509-verify",
    ],
)

rust_test(
    name = "oak_attestation_gcp_tests",
    crate = ":oak_attestation_gcp",
    data = [
        "//oak_attestation_gcp/testdata:debug_token",
        "//oak_attestation_gcp/testdata:developer_key_public_key",
        "//oak_attestation_gcp/testdata:endorsement.json",
        "//oak_attestation_gcp/testdata:endorsement_signature",
        "//oak_attestation_gcp/testdata:expired_token",
        "//oak_attestation_gcp/testdata:invalid_signature_token",
        "//oak_attestation_gcp/testdata:long_lived_token",
        "//oak_attestation_gcp/testdata:other_developer_key_public_key",
        "//oak_attestation_gcp/testdata:other_endorsement_signature",
        "//oak_attestation_gcp/testdata:policy_claims.json",
        "//oak_attestation_gcp/testdata:root_ca_cert",
        "//oak_attestation_gcp/testdata:valid_token",
    ],
    deps = [
        "//oak_file_utils",
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
    ],
)
