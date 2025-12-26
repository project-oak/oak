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

load("@rules_rust//rust:defs.bzl", "rust_binary", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_binary(
    name = "arbiter",
    testonly = True,
    srcs = ["arbiter.rs"],
    deps = [
        "//ctf_sha2/proto:arbiter_rust_proto",
        "//falsify",
        "//oak_attestation_gcp",
        "//oak_attestation_verification",
        "//oak_attestation_verification_types",
        "//oak_proto_rust",
        "//oak_time",
        "//tr/key_util",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:clap",
        "@oak_crates_index//:env_logger",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:jwt",
        "@oak_crates_index//:log",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:x509-cert",
    ],
)

rust_test(
    name = "arbiter_tests",
    crate = ":arbiter",
    deps = [
        "//oak_attestation_verification",
        "//oak_dice",
        "//oak_time",
        "//oak_time:oak_time_std",
        "//tr/key_util",
        "@oak_crates_index//:base64",
        "@oak_crates_index//:coset",
        "@oak_crates_index//:jwt",
        "@oak_crates_index//:openssl",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:x509-cert",
    ],
)
