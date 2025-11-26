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

load("@rules_cc//cc:defs.bzl", "cc_library")
load("@rules_rust//rust:defs.bzl", "rust_library", "rust_test")

package(
    default_visibility = ["//:internal"],
    licenses = ["notice"],
)

exports_files(["layout.ld"])

_OAK_RESTRICTED_KERNEL_COMMON_DEPS = [
    "//oak_channel",
    "//oak_core",
    "//oak_crypto",
    "//oak_dice",
    "//oak_linux_boot_params",
    "//oak_restricted_kernel_dice",
    "//oak_restricted_kernel_interface",
    "//oak_sev_guest",
    "//sev_serial",
    "@oak_crates_index//:acpi",
    "@oak_crates_index//:aml",
    "@oak_crates_index//:anyhow",
    "@oak_crates_index//:arrayvec",
    "@oak_crates_index//:atomic_refcell",
    "@oak_crates_index//:bitflags",
    "@oak_crates_index//:bitvec",
    "@oak_crates_index//:coset",
    "@oak_crates_index//:goblin",
    "@oak_crates_index//:hex",
    "@oak_crates_index//:hpke",
    "@oak_crates_index//:libm",
    "@oak_crates_index//:linked_list_allocator",
    "@oak_crates_index//:log",
    "@oak_crates_index//:p256",
    "@oak_crates_index//:self_cell",
    "@oak_crates_index//:static_assertions",
    "@oak_crates_index//:spinning_top",
    "@oak_crates_index//:strum",
    "@oak_crates_index//:x86_64",
    "@oak_crates_index//:zerocopy",
    "@oak_crates_index//:zeroize",
]

cc_library(
    name = "bootstrap",
    srcs = ["boot.s"],
    linkstatic = True,
)

rust_library(
    name = "oak_restricted_kernel_virtio_console_channel",
    srcs = glob(["src/**/*.rs"]),
    crate_features = [
        "virtio_console_channel",
    ],
    crate_name = "oak_restricted_kernel",
    target_compatible_with = [
        "//:x86_64-none-setting",
    ],
    deps = _OAK_RESTRICTED_KERNEL_COMMON_DEPS + [
        ":bootstrap",
        "@oak_crates_index//:virtio-drivers",
    ],
)

rust_library(
    name = "oak_restricted_kernel_simple_io_channel",
    srcs = glob(["src/**/*.rs"]),
    crate_features = [
        "simple_io_channel",
    ],
    crate_name = "oak_restricted_kernel",
    target_compatible_with = [
        "//:x86_64-none-setting",
    ],
    deps = _OAK_RESTRICTED_KERNEL_COMMON_DEPS + [
        ":bootstrap",
        "//oak_simple_io",
    ],
)

[
    rust_test(
        name = "oak_restricted_kernel_%s_test" % feature,
        crate = ":oak_restricted_kernel_%s" % feature,
        crate_features = [
            feature,
        ],
        # So we can do `bazel build //oak_restricted_kernel:all --platforms=//:x86_64-unknown-none`:
        platform = "//:x86_64-linux",
        deps = [
            "@oak_crates_index//:assertables",
        ],
    )
    for feature in [
        "virtio_console_channel",
        "simple_io_channel",
    ]
]
