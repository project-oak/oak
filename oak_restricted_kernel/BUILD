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
    default_visibility = ["//visibility:public"],
    licenses = ["notice"],
)

_OAK_RESTRICTED_KERNEL_DEPS = [
    "//oak_channel",
    "//oak_core",
    "//oak_crypto",
    "//oak_dice",
    "//oak_linux_boot_params",
    "//oak_restricted_kernel_dice",
    "//oak_restricted_kernel_interface",
    "//oak_sev_guest",
    "//oak_simple_io",
    "//oak_virtio",
    "//sev_serial",
    "//third_party/rust-hypervisor-firmware-virtio",
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
    "@oak_crates_index//:spinning_top",
    "@oak_crates_index//:static_assertions",
    "@oak_crates_index//:strum",
    "@oak_crates_index//:uart_16550",
    "@oak_crates_index//:virtio-drivers",
    "@oak_crates_index//:x86_64",
    "@oak_crates_index//:zerocopy",
    "@oak_crates_index//:zeroize",
]

rust_library(
    name = "oak_restricted_kernel",
    srcs = glob(["src/**/*.rs"]),
    compile_data = ["src/boot/boot.s"],
    crate_features = [
        "virtio_console_channel",
    ],
    deps = _OAK_RESTRICTED_KERNEL_DEPS,
)

rust_library(
    name = "oak_restricted_kernel_simple_io_channel",
    srcs = glob(["src/**/*.rs"]),
    compile_data = ["src/boot/boot.s"],
    crate_features = [
        "simple_io_channel",
    ],
    deps = _OAK_RESTRICTED_KERNEL_DEPS,
)

rust_test(
    name = "oak_restricted_kernel_test",
    crate = ":oak_restricted_kernel",
    crate_features = [
        "simple_io_channel",
    ],
    deps = [
        "@oak_crates_index//:assertables",
    ],
)

rust_test(
    name = "oak_restricted_kernel_sinmple_io_channel_test",
    crate = ":oak_restricted_kernel_simple_io_channel",
    crate_features = [
        "simple_io_channel",
    ],
    deps = [
        "@oak_crates_index//:assertables",
    ],
)
