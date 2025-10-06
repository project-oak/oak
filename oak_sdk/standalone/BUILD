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
    name = "oak_sdk_standalone",
    srcs = [
        "standalone.rs",
    ],
    deps = [
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_attestation_verification:oak_attestation_verification_results",
        "//oak_containers/attestation",
        "//oak_crypto",
        "//oak_dice",
        "//oak_proto_rust",
        "//oak_sdk/common:oak_sdk_common",
        "//stage0_dice",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
    ],
)

rust_test(
    name = "oak_sdk_standalone_test",
    crate = ":oak_sdk_standalone",
    deps = [
        "//oak_attestation_verification",
        "//oak_attestation_verification_types",
        "//oak_time:oak_time_std",
    ],
)

rust_library(
    name = "ffi",
    testonly = True,
    srcs = [
        "ffi/standalone_c.rs",
    ],
    deps = [
        ":oak_sdk_standalone",
        "//oak_crypto",
        "//oak_ffi:oak_ffi_bytes",
        "//oak_proto_rust",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:prost",
    ],
)
