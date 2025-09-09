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

load("@rules_rust//rust:defs.bzl", "rust_binary")
load("//oak_attestation_verification_cli:defs.bzl", "attestation_verification_report")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "generator",
    testonly = True,
    srcs = glob(["*.rs"]),
    deps = [
        "//oak_attestation_gcp",
        "//oak_attestation_verification",
        "//oak_proto_rust",
        "//oak_proto_rust/oak_proto_rust_lib",
        "//oak_time",
        "//tr/intoto",
        "//trex/sigstore",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:chrono",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:jwt",
        "@oak_crates_index//:openssl",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:serde_json",
        "@oak_crates_index//:sha2",
    ],
)

genrule(
    name = "attestation_verification_report_input_files",
    testonly = True,
    outs = [
        "collected_attestation.binpb",
        "reference_values.binpb",
    ],
    cmd = """
    $(location :generator) \
        --collected-attestation-out=$(location :collected_attestation.binpb) \
        --reference-values-out=$(location :reference_values.binpb)
    """,
    tools = [":generator"],
)

attestation_verification_report(
    name = "report",
    attestation = ":collected_attestation.binpb",
    reference_values = ":reference_values.binpb",
)
