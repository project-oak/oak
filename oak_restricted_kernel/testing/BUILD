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

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

rust_binary(
    name = "test_orchestrator",
    srcs = [
        "test_orchestrator.rs",
    ],
    platform = "//:x86_64-unknown-none",
    rustc_flags = [
        "--codegen=link-arg=-Wl,-zmax-page-size=0x200000",
    ],
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        "//oak_dice",
        "//oak_restricted_kernel_dice",
        "//oak_restricted_kernel_interface",
        "//oak_restricted_kernel_sdk",
        "@oak_crates_index//:hex",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)

rust_binary(
    name = "enclave_app",
    srcs = [
        "enclave_app.rs",
    ],
    platform = "//:x86_64-unknown-none",
    rustc_flags = [
        "--codegen=link-arg=-Wl,-zmax-page-size=0x200000",
    ],
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        "//oak_dice",
        "//oak_restricted_kernel_interface",
        "//oak_restricted_kernel_sdk",
        "@oak_crates_index//:zerocopy",
        "@oak_crates_index//:zeroize",
    ],
)

rust_test(
    name = "key_handling_test",
    srcs = [
        "key_handling_test.rs",
    ],
    args = ["--test-threads=1"],
    data = [
        ":test_orchestrator",
        "//oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_serial_channel_bin",
        "//stage0_bin",
    ],
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        "//oak_file_utils",
        "//oak_test_utils",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:googletest",
    ],
)

rust_test(
    name = "orchestrator_key_handling_test",
    srcs = [
        "orchestrator_key_handling_test.rs",
    ],
    args = ["--test-threads=1"],
    data = [
        ":enclave_app",
        "//enclave_apps/oak_orchestrator:insecure_oak_orchestrator_fixed_key",
        "//oak_restricted_kernel_wrapper:oak_restricted_kernel_wrapper_virtio_console_channel_bin",
        "//stage0_bin",
    ],
    target_compatible_with = ["@platforms//cpu:x86_64"],
    deps = [
        "//oak_crypto",
        "//oak_file_utils",
        "//oak_test_utils",
        "@oak_crates_index//:anyhow",
        "@oak_crates_index//:googletest",
        "@oak_crates_index//:sha2",
    ],
)
