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
    name = "oak_session_ffi_server_session",
    srcs = [
        "server_session.rs",
    ],
    deps = [
        "//oak_ffi:oak_ffi_bytes",
        "//oak_ffi:oak_ffi_error",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:prost",
    ],
)

rust_library(
    name = "oak_session_ffi_client_session",
    srcs = [
        "client_session.rs",
    ],
    deps = [
        "//oak_ffi:oak_ffi_bytes",
        "//oak_ffi:oak_ffi_error",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:prost",
    ],
)

rust_library(
    name = "oak_session_ffi_config",
    srcs = ["config.rs"],
    deps = [
        "//oak_attestation_types",
        "//oak_attestation_verification_types",
        "//oak_crypto",
        "//oak_ffi:oak_ffi_bytes",
        "//oak_ffi:oak_ffi_error",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:p256",
    ],
)

rust_library(
    name = "oak_session_ffi_attestation",
    srcs = ["attestation.rs"],
    deps = [
        ":oak_session_ffi_config",
        "//oak_attestation_types",
        "//oak_ffi:oak_ffi_bytes",
        "//oak_ffi:oak_ffi_error",
        "//oak_proto_rust",
        "//oak_sdk/common:oak_sdk_common",
        "@oak_crates_index//:prost",
    ],
)

rust_library(
    name = "oak_session_ffi_testing",
    srcs = ["testing.rs"],
    deps = [
        ":oak_session_ffi_config",
        "//oak_attestation_types",
        "//oak_attestation_verification_types",
        "//oak_ffi:oak_ffi_bytes",
        "//oak_proto_rust",
        "//oak_sdk/common:oak_sdk_common",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:rand_core",
    ],
)

rust_test(
    name = "tests",
    srcs = ["tests.rs"],
    deps = [
        ":oak_session_ffi_attestation",
        ":oak_session_ffi_client_session",
        ":oak_session_ffi_config",
        ":oak_session_ffi_server_session",
        ":oak_session_ffi_testing",
        "//oak_crypto",
        "//oak_ffi:oak_ffi_bytes",
        "//oak_proto_rust",
        "//oak_session",
        "@oak_crates_index//:prost",
    ],
)
