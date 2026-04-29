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
    name = "verify_endorsement",
    srcs = glob(["**/*.rs"]),
    deps = [
        "//oak_proto_rust",
        "//oak_time",
        "//tr/c2sp",
        "//tr/intoto",
        "//tr/key_util",
        "//tr/pes",
        "//tr/rekor",
        "//util/digest:oak_digest",
        "@oak_crates_index//:anyhow",
    ],
)

rust_test(
    name = "verify_endorsement_tests",
    crate = ":verify_endorsement",
    data = [
        "//oak_attestation_verification/testdata:endorsement",
    ],
    target_compatible_with = ["@platforms//os:linux"],
    deps = [
        "//oak_attestation_verification:test_util",
        "//oak_crypto:oak_crypto_tink",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:ed25519-dalek",
        "@oak_crates_index//:sha2",
    ],
)
