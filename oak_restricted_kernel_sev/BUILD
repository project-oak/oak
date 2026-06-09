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

load("@rules_rust//rust:defs.bzl", "rust_library")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

_OAK_RESTRICTED_KERNEL_SEV_COMMON_DEPS = [
    "//oak_hal",
    "//oak_core",
    "//oak_sev_guest",
    "//oak_linux_boot_params",
    "@oak_crates_index//:log",
    "@oak_crates_index//:spinning_top",
    "@oak_crates_index//:static_assertions",
    "@oak_crates_index//:x86_64",
    "@oak_crates_index//:zerocopy",
]

rust_library(
    name = "oak_restricted_kernel_sev_virtio_console_channel",
    srcs = glob(["src/**/*.rs"]),
    crate_name = "oak_restricted_kernel_sev",
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
        "//bazel/rust:avx_ON",
    ],
    deps = _OAK_RESTRICTED_KERNEL_SEV_COMMON_DEPS + [
        "//oak_restricted_kernel:oak_restricted_kernel_virtio_console_channel",
    ],
)

rust_library(
    name = "oak_restricted_kernel_sev_simple_io_channel",
    srcs = glob(["src/**/*.rs"]),
    crate_name = "oak_restricted_kernel_sev",
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
        "//bazel/rust:avx_ON",
    ],
    deps = _OAK_RESTRICTED_KERNEL_SEV_COMMON_DEPS + [
        "//oak_restricted_kernel:oak_restricted_kernel_simple_io_channel",
    ],
)

rust_library(
    name = "oak_restricted_kernel_sev_serial_channel",
    srcs = glob(["src/**/*.rs"]),
    crate_name = "oak_restricted_kernel_sev",
    target_compatible_with = [
        "@platforms//cpu:x86_64",
        "@platforms//os:none",
        "//bazel/rust:avx_ON",
    ],
    deps = _OAK_RESTRICTED_KERNEL_SEV_COMMON_DEPS + [
        "//oak_restricted_kernel:oak_restricted_kernel_serial_channel",
    ],
)
