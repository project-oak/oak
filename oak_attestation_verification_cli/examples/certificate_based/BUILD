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
        "//cc/crypto/tink/signature/testing:signature-ffi",
        "//oak_ffi:cxx_string",
        "//oak_ffi:oak_ffi_bytes",
        "//oak_proto_rust",
        "//oak_time",
        "//oak_time:oak_time_std",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:rand_core",
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
