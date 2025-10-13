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

load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_session",
    srcs = glob(["src/*.rs"]),
    proc_macro_deps = [
        "@oak_crates_index//:async-trait",
    ],
    deps = [
        "//oak_attestation_types",
        "//oak_attestation_verification:oak_attestation_verification_results",
        "//oak_attestation_verification_types",
        "//oak_crypto",
        "//oak_proto_rust",
        "//oak_time",
        "@oak_crates_index//:aead",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:derive_builder",
        "@oak_crates_index//:itertools",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:sha2",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:thiserror",
    ],
)

rust_test(
    name = "oak_session_tests",
    srcs = glob(["src/tests/*.rs"]),
    crate_root = "src/tests/mod.rs",
    deps = [
        ":oak_session",
        ":oak_session_testing",
        "//oak_attestation_types",
        "//oak_attestation_verification_types",
        "//oak_crypto",
        "//oak_proto_rust",
        "//oak_time",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:mockall",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:proptest",
        "@oak_crates_index//:rand_core",
        "@oak_crates_index//:tokio",
    ],
)

rust_library(
    name = "oak_session_testing",
    testonly = True,
    srcs = glob(["testing/*.rs"]),
    deps = [
        ":oak_session",
        "//oak_attestation_types",
        "//oak_attestation_verification_types",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:googletest",
    ],
)
