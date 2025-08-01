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

load("@rules_rust//rust:defs.bzl", "rust_library")
load("//bazel:defs.bzl", "any_platform")

package(
    default_visibility = ["//:default_visibility"],
    licenses = ["notice"],
)

rust_library(
    name = "oak_restricted_kernel_sdk",
    srcs = glob(["src/*.rs"]),
    # Only enable the testing feature on Linux for unit and integration tests.
    crate_features = select({
        "@platforms//os:linux": ["testing"],
        "//conditions:default": [],
    }),
    proc_macro_deps = [
        "//oak_restricted_kernel_sdk_proc_macro",
    ],
    target_compatible_with = any_platform([
        "//:x86_64-linux-setting",  # Needed to run unit tests.
        "//:x86_64-none-setting",
    ]),
    deps = [
        "//micro_rpc",
        "//oak_attestation",
        "//oak_attestation_types",
        "//oak_attestation_verification",
        "//oak_channel",
        "//oak_core",
        "//oak_crypto",
        "//oak_dice",
        "//oak_enclave_runtime_support",
        "//oak_proto_rust",
        "//oak_restricted_kernel_dice",
        "//oak_restricted_kernel_interface",
        "//oak_session",
        "//stage0_dice",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:lazy_static",
        "@oak_crates_index//:log",
        "@oak_crates_index//:p256",
        "@oak_crates_index//:prost",
        "@oak_crates_index//:prost-types",
        "@oak_crates_index//:strum",
        "@oak_crates_index//:zerocopy",
    ],
)
