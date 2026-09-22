#
# Copyright 2026 The Project Oak Authors
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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")

package(licenses = ["notice"])

# Runs anywhere, including on a laptop with no TEE.
rust_binary(
    name = "oak_trusted_agent_provenance_verifier",
    srcs = [
        "main.rs",
        "report.rs",
        "tests.rs",
        "workload.rs",
    ],
    target_compatible_with = ["@platforms//os:linux"],
    visibility = ["//visibility:public"],
    deps = [
        "//oak_attestation_gcp",
        "//oak_attestation_verification_types",
        "//oak_proto_rust",
        "//oak_time",
        "//oak_trusted_agent/provenance/common",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:jwt",
        "@oak_crates_index//:oci-spec",
        "@oak_crates_index//:prost",
    ],
)

rust_test(
    name = "oak_trusted_agent_provenance_verifier_test",
    crate = ":oak_trusted_agent_provenance_verifier",
    target_compatible_with = ["@platforms//os:linux"],
)
